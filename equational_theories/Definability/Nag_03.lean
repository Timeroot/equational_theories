import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op y x) = (M.op y y) := by grind
      have b0e20 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
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
      have b0e44 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 y y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ y) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e47
      have b0e51 : (M.op y y) = (k x y) := by grind
      clear b0e44
      have b0e52 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e50
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e50
        | exact resolve b0e50 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50
      have b0e53 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e52
           have i₂ := b0e51
           grind)
        | exact superpose b0e51 b0e52
        | exact resolve b0e52 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51 b0e52
      have b0e72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e16 X1 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op X1 X0) (M.op X1 X1)
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e83 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e72 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72
      have b0e661 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e83 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83
      have b0e664 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e661 X0 X1
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e661 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e661 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e661 X0 X1
           have r₂ := b0e16 (M.op X1 X0) (M.op X1 X1)
           grind)
        | exact resolve b0e661 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e661
      have b0e686 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X0 X1
           have i₂ := b0e664 X1 (τ X0)
           grind)
        | exact superpose b0e664 b0e23
        | (have j1 := b0e664 (k (σ X1) X0) (σ (M.op (τ X0) X1))
           grind)
        | exact resolve b0e23 b0e664
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e687 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e664 (σ X1) (σ X0)
           grind)
        | exact superpose b0e664 b0e17
        | (have j1 := b0e664 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
           grind)
        | exact resolve b0e17 b0e664
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e664
      have b0e5981 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e686 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e686
        | exact resolve b0e686 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e686
      have b0e6016 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e5981 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e5981
        | (have j0 := b0e5981 (σ (k X1 X0)) (σ (M.op X0 X1))
           grind)
        | exact resolve b0e5981 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5981
      have b0e20829 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e687 x y
           grind)
        | exact superpose b0e687 b0e18
        | (have j1 := b0e687 x y
           grind)
        | exact resolve b0e18 b0e687
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e687
      have b0e20960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e20829
           have i₂ := b0e6016 x y
           grind)
        | exact superpose b0e6016 b0e20829
        | (have j1 := b0e6016 (σ x) (σ y)
           grind)
        | (have r₁ := b0e20829
           have r₂ := b0e6016 x y
           grind)
        | (have r₁ := b0e20829
           have r₂ := b0e6016 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e20829
           have r₂ := b0e6016 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e20829 b0e6016
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6016 b0e20829
      have b0e20961 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e20960
      have b0e21983 : x = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e12 x
           have i₂ := b0e20961
           grind)
        | exact superpose b0e20961 b0e12
        | exact resolve b0e12 b0e20961
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20961
      have b0e22029 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e21983
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e21983
        | exact resolve b0e21983 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21983
      have b0e22030 : x = y := by grind
      clear b0e22029
      have b0e23468 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e22030
           grind)
        | exact superpose b0e22030 b0e18
        | exact resolve b0e18 b0e22030
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22030
      have b0e23470 : False := by grind
      exact b0e23470
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op y x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e53 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k x y) := by
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
        have b2e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e58 : (M.op y y) = (k x y) := by grind
        clear b2e53
        have b2e60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e57 (σ X0)
             grind)
          | exact superpose b2e57 b2e18
          | exact resolve b2e18 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e60 X0
             have i₂ := b2e57 X0
             grind)
          | exact superpose b2e57 b2e60
          | exact resolve b2e60 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e60
        have b2e78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
        have b2e96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e78 X0 X1
             have i₂ := b2e67 X0
             grind)
          | exact superpose b2e67 b2e78
          | (have j0 := b2e78 X0 X1
             grind)
          | exact resolve b2e78 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e78
        have b2e1190 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e96 y x
             grind)
          | exact superpose b2e96 b2e21
          | (have j1 := b2e96 y x
             grind)
          | exact resolve b2e21 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96
        have b2e1247 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have r₁ := b2e1190
             have r₂ := b2e22
             grind)
          | exact resolve b2e1190 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1190
        have b2e1261 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1247
             have i₂ := b2e58
             grind)
          | exact superpose b2e58 b2e1247
          | exact resolve b2e1247 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58 b2e1247
        have b2e1267 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have r₁ := b2e1261
             have r₂ := b2e67 y
             grind)
          | exact resolve b2e1261 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1261
        have b2e1272 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1267
             grind)
          | exact superpose b2e1267 b2e21
          | exact resolve b2e21 b2e1267
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1267
        have b2e1288 : False := by grind
        exact b2e1288
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e55 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e55
        have b6e59 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e58
          | exact resolve b6e58 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e103 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e59
             grind)
          | exact superpose b6e59 b6e15
          | exact resolve b6e15 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e105 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e103
        have b6e106 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e105
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e105
          | exact resolve b6e105 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e105
        have b6e107 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e106
             have i₂ := b6e57 y
             grind)
          | exact superpose b6e57 b6e106
          | exact resolve b6e106 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57 b6e106
        have b6e158 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e107
             grind)
          | exact superpose b6e107 b6e13
          | exact resolve b6e13 b6e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e107
        have b6e159 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e158
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e158
          | exact resolve b6e158 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e158
        have b6e215 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e159
             grind)
          | exact superpose b6e159 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e159
        have b6e216 : (M.op y x) = (M.op y y) ∨ x = y := by grind
        clear b6e215
        have b6e218 : x = y := by
          first
          | (have r₁ := b6e216
             have r₂ := b6e20
             grind)
          | exact resolve b6e216 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e216
        have b6e220 : False := by grind
        exact b6e220
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
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
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
          have b8e68 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X1 X0) (M.op X1 X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e79 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e68 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e624 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e79 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e627 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e624 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e624 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e624 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e624 X0 X1
               have r₂ := b8e18 (M.op X1 X0) (M.op X1 X1)
               grind)
            | exact resolve b8e624 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e624
          have b8e647 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e627 (σ X1) (σ X0)
               grind)
            | exact superpose b8e627 b8e19
            | (have j1 := b8e627 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e627
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e649 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e627 (τ X1) X0
               grind)
            | exact superpose b8e627 b8e26
            | (have j1 := b8e627 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
               grind)
            | exact resolve b8e26 b8e627
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e627
          have b8e3777 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e649 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e649
            | exact resolve b8e649 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e649
          have b8e3843 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e3777 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e3777
            | (have j0 := b8e3777 (σ (k X0 X1)) (σ (M.op X1 X0))
               grind)
            | exact resolve b8e3777 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3777
          have b8e16106 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e647 x y
               grind)
            | exact superpose b8e647 b8e20
            | (have j1 := b8e647 x y
               grind)
            | exact resolve b8e20 b8e647
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e647
          have b8e16194 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e16106
               have r₂ := b8e24
               grind)
            | exact resolve b8e16106 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16106
          have b8e17070 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e16194
               have i₂ := b8e3843 y x
               grind)
            | exact superpose b8e3843 b8e16194
            | (have j1 := b8e3843 x y
               grind)
            | (have r₁ := b8e16194
               have r₂ := b8e3843 y x
               grind)
            | (have r₁ := b8e16194
               have r₂ := b8e3843 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e16194
               have r₂ := b8e3843 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e16194 b8e3843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3843 b8e16194
          have b8e17071 : x = y := by grind
          clear b8e17070
          have b8e17076 : False := by grind
          exact b8e17076

/-- `Equation546`: `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pxy_y_pyx_Equation546 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law546 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law546.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e38 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) X0
           grind)
        | (have r₁ := b0e14 (σ x) x
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x x
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have j0 := b0e39 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e41 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e38 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e66 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e41 (σ X0)
           grind)
        | exact superpose b0e41 b0e17
        | exact resolve b0e17 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e68 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e66 X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e66
        | exact resolve b0e66 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e66
      have b0e381 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e68 y
           grind)
        | exact superpose b0e68 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e68 y
           grind)
        | exact resolve b0e18 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e392 : False := by grind
      exact b0e392
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x X0
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b1e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e41 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e42 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e41
        have b1e43 : (σ y) = (k (σ x) (σ y)) := by
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
          | (have i₁ := b1e43
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e43
          | exact resolve b1e43 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e46 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e45
             have i₂ := b1e38 y
             grind)
          | exact superpose b1e38 b1e45
          | exact resolve b1e45 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e45
        have b1e47 : False := by grind
        exact b1e47
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e34 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x x
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b2e34 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e524 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e50 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e525 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e524 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e524
        have b2e9854 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e525 x
             have i₂ := b2e35 x
             grind)
          | exact superpose b2e35 b2e525
          | (have j0 := b2e525 x
             grind)
          | exact resolve b2e525 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e525
        have b2e9860 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have r₁ := b2e9854
             have r₂ := b2e21
             grind)
          | exact resolve b2e9854 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9854
        have b2e9866 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e9860
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e9860
          | exact resolve b2e9860 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9860
        have b2e9867 : False := by grind
        exact b2e9867
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e15 (σ x) x
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e45 : y ≠ y ∨ x = (M.op x x) ∨ y = (k x y) := by
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
        have b3e47 : x = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e45
        have b3e48 : y = (k x y) := by
          first
          | (have r₁ := b3e47
             have r₂ := b3e20
             grind)
          | exact resolve b3e47 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e74 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e38 (σ X0)
             grind)
          | exact superpose b3e38 b3e18
          | exact resolve b3e18 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e486 : (σ y) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e74 y
             grind)
          | exact superpose b3e74 b3e23
          | exact resolve b3e23 b3e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e74
        have b3e501 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e486
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e486
          | exact resolve b3e486 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e486
        have b3e502 : False := by grind
        exact b3e502
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e31 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op X1 X0) X0
               have i₂ := b5e13 X0 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : x = (M.op y y) := by
            first
            | (have i₁ := b5e31 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e31
            | exact resolve b5e31 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e55 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e18 X0 X2
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X0 X1
               have j1 := b5e18 X0 X2
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e55 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e392 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e58 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e30421 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e392 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e392
          have b5e30426 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e30421 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e30421 X0
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e30421 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30421
          have b5e30625 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e30426 (σ X0)
               grind)
            | exact superpose b5e30426 b5e19
            | exact resolve b5e19 b5e30426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30636 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e30625 X0
               have i₂ := b5e30426 X0
               grind)
            | exact superpose b5e30426 b5e30625
            | exact resolve b5e30625 b5e30426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30426 b5e30625
          have b5e31183 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e31 (σ X0) (σ X0)
               have i₂ := b5e30636 X0
               grind)
            | exact superpose b5e30636 b5e31
            | exact resolve b5e31 b5e30636
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e30636
          have b5e34299 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e31183 y
               have i₂ := b5e32
               grind)
            | exact superpose b5e32 b5e31183
            | exact resolve b5e31183 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e31183
          have b5e34429 : False := by grind
          exact b5e34429
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e34 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) x
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e34 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e37 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e35 (σ X0)
             grind)
          | exact superpose b6e35 b6e18
          | exact resolve b6e18 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e95 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e37 x
             grind)
          | exact superpose b6e37 b6e22
          | exact resolve b6e22 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e128 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e95
             grind)
          | exact superpose b6e95 b6e13
          | exact resolve b6e13 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e130 : x = (k x x) := by
          first
          | (have i₁ := b6e128
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e128
          | exact resolve b6e128 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e128
        have b6e224 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e130
             grind)
          | exact superpose b6e130 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e130
        have b6e225 : x = (M.op x x) := by grind
        clear b6e224
        have b6e227 : False := by grind
        exact b6e227
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e34 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 (M.op X0 (M.op X1 X2)) X1
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (M.op X1 X0) X0
               have i₂ := b7e13 X0 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e35 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e35
            | exact resolve b7e35 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op X1 (M.op X2 X0)) X0 X2
               have i₂ := b7e35 (M.op X2 X0) X1
               grind)
            | exact superpose b7e35 b7e13
            | exact resolve b7e13 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e45 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e49 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e51 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e49
               have r₂ := b7e23
               grind)
            | exact resolve b7e49 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e52 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e51
            | exact resolve b7e51 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e55 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e52
               grind)
            | exact superpose b7e52 b7e14
            | exact resolve b7e14 b7e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e56 : y = (k x y) := by
            first
            | (have i₁ := b7e55
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e55
            | exact resolve b7e55 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e61 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 X0
               have i₂ := b7e18 (σ X1) (σ X0)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X1) (σ X1)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e16 X0 X1
               have i₂ := b7e18 X0 X2
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X0 X1
               have j1 := b7e18 X0 X2
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X1 X1
               have r₂ := b7e18 X1 X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e71 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e67 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e75 : y = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e56
               grind)
            | exact superpose b7e56 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e76 : y = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e21
               grind)
            | exact resolve b7e75 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e78 : y = (M.op y x) := by
            first
            | (have r₁ := b7e76
               have r₂ := b7e22
               grind)
            | exact resolve b7e76 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e108 : ∀ X0 : G, (M.op (M.op x (M.op y X0)) y) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 x y X0
               have i₂ := b7e78
               grind)
            | exact superpose b7e78 b7e34
            | exact resolve b7e34 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e78
          have b7e266 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 y))) = (M.op (M.op x X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b7e108 (M.op X1 (M.op X0 (M.op X1 y)))
               have i₂ := b7e13 X0 y X1
               grind)
            | exact superpose b7e13 b7e108
            | exact resolve b7e108 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e339 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e71 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e499 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e61 y y
               have i₂ := b7e36
               grind)
            | exact superpose b7e36 b7e61
            | exact resolve b7e61 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e546 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e499
          have b7e27365 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e339 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e339
          have b7e27374 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e27365 X0
               have j1 := b7e16 X0 X0
               grind)
            | (have r₁ := b7e27365 X0
               have r₂ := b7e16 X0 x
               grind)
            | exact resolve b7e27365 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27365
          have b7e27593 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e27374 (σ X0)
               grind)
            | exact superpose b7e27374 b7e19
            | exact resolve b7e19 b7e27374
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e27609 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e27593 X0
               have i₂ := b7e27374 X0
               grind)
            | exact superpose b7e27374 b7e27593
            | exact resolve b7e27593 b7e27374
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27593
          have b7e30366 : (M.op (σ x) (σ x)) = (σ (M.op (k y y) (k y y))) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e27609 (k y y)
               have i₂ := b7e546
               grind)
            | exact superpose b7e546 b7e27609
            | exact resolve b7e27609 b7e546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e546 b7e27609
          have b7e30514 : (M.op (σ x) (σ x)) = (σ (M.op (M.op y y) (M.op y y))) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e30366
               have i₂ := b7e27374 y
               grind)
            | exact superpose b7e27374 b7e30366
            | exact resolve b7e30366 b7e27374
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27374 b7e30366
          have b7e30555 : (M.op (σ x) (σ x)) = (σ (M.op y (M.op y (M.op y y)))) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e30514
               have i₂ := b7e39 (M.op y y) y y
               grind)
            | (have i₁ := b7e30514
               have i₂ := b7e39 y (M.op y y) y
               grind)
            | exact superpose b7e39 b7e30514
            | exact resolve b7e30514 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e30514
          have b7e30580 : (M.op (σ x) (σ x)) = (σ (M.op (M.op x y) y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e30555
               have i₂ := b7e266 y y
               grind)
            | exact superpose b7e266 b7e30555
            | exact resolve b7e30555 b7e266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e266 b7e30555
          have b7e30598 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e30580
               have i₂ := b7e35 y x
               grind)
            | exact superpose b7e35 b7e30580
            | exact resolve b7e30580 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e30580
          have b7e30609 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e30598
               have r₂ := b7e23
               grind)
            | exact resolve b7e30598 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30598
          have b7e30628 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e36
               have i₂ := b7e30609
               grind)
            | exact superpose b7e30609 b7e36
            | exact resolve b7e36 b7e30609
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e30609
          have b7e30691 : False := by grind
          exact b7e30691
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b8e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) (M.op X2 (M.op X3 X0))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X3 (M.op X1 (M.op X0 (M.op X1 X2))) X2
               have i₂ := b8e13 X0 X2 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X2 (M.op X0 (M.op X1 X2)) X1
               have i₂ := b8e13 X0 X2 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e33 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op X1 X0) X0
               have i₂ := b8e13 X0 X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X2 X1)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e33 (M.op X2 (M.op X0 (M.op X2 X1))) X1
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e33
            | exact resolve b8e33 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X1 (M.op X2 X0)) X0 X2
               have i₂ := b8e33 (M.op X2 X0) X1
               grind)
            | exact superpose b8e33 b8e13
            | exact resolve b8e13 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b8e58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e60 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e18 X1 (τ X0)
               grind)
            | exact superpose b8e18 b8e26
            | (have j1 := b8e18 X1 X1
               grind)
            | exact resolve b8e26 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X2
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e18 X0 X2
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) X0
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 (σ x) X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) x
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ x)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have j0 := b8e66 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e68 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e65 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e82 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X3 X2))) = (M.op (M.op X1 X0) (M.op X2 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e32 X1 X2 (M.op X3 (M.op X0 (M.op X3 X2)))
               have i₂ := b8e13 X0 X2 X3
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e91 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X0 X1) X2)) X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X1 (M.op X0 X1) X2
               have i₂ := b8e33 X1 X0
               grind)
            | exact superpose b8e33 b8e32
            | exact resolve b8e32 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e92 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op X2 (M.op X1 X0)) X3)) X0) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e32 (M.op X1 X2) (M.op X2 (M.op X1 X0)) X3
               have i₂ := b8e32 X2 X1 X0
               grind)
            | exact superpose b8e32 b8e32
            | exact resolve b8e32 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e101 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = (M.op X3 (M.op X0 (M.op X3 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e82 X2 X3 X0 X1
               have i₂ := b8e36 (M.op X3 X2) X3 X0
               grind)
            | (have i₁ := b8e82 X2 X3 X0 X1
               have i₂ := b8e36 X3 (M.op X3 X2) X0
               grind)
            | exact superpose b8e36 b8e82
            | exact resolve b8e82 b8e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e127 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X2))) (M.op X1 (M.op X3 X2))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e31 X2 (M.op X0 (M.op X1 (M.op X0 X2))) X1 X3
               have i₂ := b8e31 X1 X0 X2 (M.op X0 (M.op X1 (M.op X0 X2)))
               grind)
            | exact superpose b8e31 b8e31
            | exact resolve b8e31 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e131 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X2 X0)) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X1 X4))) (M.op X4 X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e31 (M.op X2 X3) X1 X4 (M.op X3 (M.op X2 X0))
               have i₂ := b8e32 X3 X2 X0
               grind)
            | exact superpose b8e32 b8e31
            | exact resolve b8e31 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e224 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 x X0
               have i₂ := b8e67 (σ X0)
               grind)
            | exact superpose b8e67 b8e19
            | (have j1 := b8e67 (σ X0)
               grind)
            | exact resolve b8e19 b8e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e246 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e36 X1 X2 (M.op X0 X1)
               have i₂ := b8e33 X1 X0
               grind)
            | exact superpose b8e33 b8e36
            | exact resolve b8e36 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e327 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e68 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e342 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op X3 (M.op X0 (M.op X3 (M.op X2 X1)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e91 X2 X1 (M.op X3 (M.op X0 (M.op X3 (M.op X2 X1))))
               have i₂ := b8e13 X0 (M.op X2 X1) X3
               grind)
            | exact superpose b8e13 b8e91
            | exact resolve b8e91 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e343 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op X3 (M.op (M.op X2 X1) (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e91 X2 X1 (M.op X3 (M.op (M.op X2 X1) (M.op X3 X0)))
               have i₂ := b8e34 (M.op X2 X1) X0 X3
               grind)
            | exact superpose b8e34 b8e91
            | exact resolve b8e91 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e477 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op X3 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e246 X2 X3 (M.op X1 X0)
               have i₂ := b8e36 (M.op X2 X3) X0 X1
               grind)
            | (have i₁ := b8e246 X2 X3 (M.op X1 X0)
               have i₂ := b8e36 X0 (M.op X2 X3) X1
               grind)
            | exact superpose b8e36 b8e246
            | exact resolve b8e246 b8e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e508 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op (M.op X1 X2) X0) (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e36 (M.op (M.op X1 X2) X0) X3 X2
               have i₂ := b8e246 X1 X2 X0
               grind)
            | exact superpose b8e246 b8e36
            | exact resolve b8e36 b8e246
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e570 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) X1
               have i₂ := b8e58 X0 X0
               grind)
            | exact superpose b8e58 b8e16
            | (have j0 := b8e16 (σ X0) X1
               have j1 := b8e58 X0 X0
               grind)
            | (have r₁ := b8e16 (σ X1) X1
               have r₂ := b8e58 X0 X1
               grind)
            | (have r₁ := b8e16 (σ X0) X1
               have r₂ := b8e58 X0 X0
               grind)
            | exact resolve b8e16 b8e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e591 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e33 (σ X0) (σ X1)
               have i₂ := b8e58 X0 X1
               grind)
            | exact superpose b8e58 b8e33
            | (have j1 := b8e58 X0 X1
               grind)
            | exact resolve b8e33 b8e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e606 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e570 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e570
          have b8e615 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e606 X0 X1
               have j1 := b8e16 (σ X0) X1
               grind)
            | (have r₁ := b8e606 X0 X1
               have r₂ := b8e16 (σ X0) X1
               grind)
            | exact resolve b8e606 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e606
          have b8e1232 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X3) = (M.op X4 (M.op (M.op X2 (M.op X1 X3)) (M.op X4 X0))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e92 X3 X1 X2 (M.op X4 (M.op (M.op X2 (M.op X1 X3)) (M.op X4 X0)))
               have i₂ := b8e34 (M.op X2 (M.op X1 X3)) X0 X4
               grind)
            | exact superpose b8e34 b8e92
            | exact resolve b8e92 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34 b8e92
          have b8e1315 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) X3) = (M.op (M.op (M.op X1 X3) X0) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e1232 X0 X1 X2 X3 x
               have i₂ := b8e343 X0 (M.op X1 X3) X2 x
               grind)
            | exact superpose b8e343 b8e1232
            | exact resolve b8e1232 b8e343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1232
          have b8e1769 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X3)) (M.op X1 X4))) = (M.op (M.op X5 (M.op X3 (M.op X5 X2))) (M.op X4 X0)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e101 X4 X1 (M.op X2 (M.op X0 X3)) (M.op X5 (M.op X3 (M.op X5 X2)))
               have i₂ := b8e31 X3 X5 X2 X0
               grind)
            | exact superpose b8e31 b8e101
            | exact resolve b8e101 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31 b8e101
          have b8e1975 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X5 (M.op X3 (M.op X5 X2))) (M.op X4 X0)) = (M.op (M.op (M.op X0 X3) X4) X2) := by
            intro X0 X2 X3 X4 X5
            first
            | (have i₁ := b8e1769 X0 x X2 X3 X4 X5
               have i₂ := b8e343 X4 (M.op X0 X3) X2 x
               grind)
            | exact superpose b8e343 b8e1769
            | exact resolve b8e1769 b8e343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e343 b8e1769
          have b8e3342 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ X0) (M.op X1 (σ (k x X0))))) = X1 ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (σ x) (σ X0)
               have i₂ := b8e224 X0
               grind)
            | exact superpose b8e224 b8e13
            | (have j1 := b8e224 X0
               grind)
            | exact resolve b8e13 b8e224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3348 : ∀ X0 : G, (σ X0) = (M.op (σ (k x X0)) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e33 (σ x) (σ X0)
               have i₂ := b8e224 X0
               grind)
            | exact superpose b8e224 b8e33
            | (have j1 := b8e224 X0
               grind)
            | exact resolve b8e33 b8e224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3380 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e33 (σ X0) (σ x)
               have i₂ := b8e224 X0
               grind)
            | exact superpose b8e224 b8e33
            | (have j1 := b8e224 X0
               grind)
            | exact resolve b8e33 b8e224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e224
          have b8e4520 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 (M.op (M.op X1 X4) X0))) = (M.op (M.op X5 (M.op (M.op X3 X2) (M.op X5 X4))) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e131 (M.op (M.op X1 X4) X0) X5 X3 X2 X4
               have i₂ := b8e246 X1 X4 X0
               grind)
            | exact superpose b8e246 b8e131
            | exact resolve b8e131 b8e246
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e4525 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X0 X4)))) = (M.op (M.op X5 (M.op (M.op X2 X1) (M.op X5 (M.op X6 (M.op X3 (M.op X6 X4)))))) X0) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b8e131 (M.op X3 (M.op X0 X4)) X5 X2 X1 (M.op X6 (M.op X3 (M.op X6 X4)))
               have i₂ := b8e127 X6 X3 X4 X0
               grind)
            | exact superpose b8e127 b8e131
            | exact resolve b8e131 b8e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127 b8e131
          have b8e4745 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X0 X4)))) = (M.op (M.op (M.op (M.op X3 (M.op X6 X4)) (M.op X2 X1)) X6) X0) := by
            intro X0 X1 X2 X3 X4 X6
            first
            | (have i₁ := b8e4525 X0 X1 X2 X3 X4 x X6
               have i₂ := b8e342 (M.op X2 X1) (M.op X3 (M.op X6 X4)) X6 x
               grind)
            | exact superpose b8e342 b8e4525
            | exact resolve b8e4525 b8e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e342 b8e4525
          have b8e4750 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op (M.op X1 X4) X0))) = (M.op (M.op (M.op X1 (M.op X3 X2)) X0) X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e4520 X0 X1 X2 X3 X4 x
               have i₂ := b8e1975 X1 X4 (M.op X3 X2) X0 x
               grind)
            | exact superpose b8e1975 b8e4520
            | exact resolve b8e4520 b8e1975
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1975 b8e4520
          have b8e4923 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X0 X4)))) = (M.op (M.op (M.op (M.op X3 X6) (M.op X2 X1)) (M.op X6 X4)) X0) := by
            intro X0 X1 X2 X3 X4 X6
            first
            | (have i₁ := b8e4745 X0 X1 X2 X3 X4 X6
               have i₂ := b8e1315 (M.op X2 X1) X3 (M.op X6 X4) X6
               grind)
            | (have i₁ := b8e4745 X0 X1 X2 X3 X4 X6
               have i₂ := b8e1315 (M.op X2 X1) X3 X6 (M.op X6 X4)
               grind)
            | exact superpose b8e1315 b8e4745
            | exact resolve b8e4745 b8e1315
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1315 b8e4745
          have b8e5044 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X0 X4)))) = (M.op X1 (M.op X2 (M.op (M.op (M.op X3 X6) X0) (M.op X6 X4)))) := by
            intro X0 X1 X2 X3 X4 X6
            first
            | (have i₁ := b8e4923 X0 X1 X2 X3 X4 X6
               have i₂ := b8e4750 (M.op X6 X4) (M.op X3 X6) X1 X2 X0
               grind)
            | exact superpose b8e4750 b8e4923
            | exact resolve b8e4923 b8e4750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4750 b8e4923
          have b8e5102 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X0 X4)))) = (M.op X1 (M.op X2 (M.op X4 (M.op X0 X3)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e5044 X0 X1 X2 X3 X4 x
               have i₂ := b8e508 X0 X3 x X4
               grind)
            | exact superpose b8e508 b8e5044
            | exact resolve b8e5044 b8e508
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e508 b8e5044
          have b8e16773 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b8e327 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e327
          have b8e16776 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16773 X0
               have j1 := b8e16 X0 X0
               grind)
            | (have r₁ := b8e16773 X0
               have r₂ := b8e16 X0 x
               grind)
            | exact resolve b8e16773 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16773
          have b8e16907 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e615 X0 X1
               have i₂ := b8e16776 X0
               grind)
            | exact superpose b8e16776 b8e615
            | (have j0 := b8e615 X0 X1
               grind)
            | exact resolve b8e615 b8e16776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e615
          have b8e16918 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e16776 (σ X0)
               grind)
            | exact superpose b8e16776 b8e19
            | exact resolve b8e19 b8e16776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e16924 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e49 X0 X0
               have i₂ := b8e16776 (τ X0)
               grind)
            | exact superpose b8e16776 b8e49
            | exact resolve b8e49 b8e16776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e16931 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e16924 X0
               have i₂ := b8e16776 X0
               grind)
            | exact superpose b8e16776 b8e16924
            | exact resolve b8e16924 b8e16776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16924
          have b8e16937 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e16918 X0
               have i₂ := b8e16776 X0
               grind)
            | exact superpose b8e16776 b8e16918
            | exact resolve b8e16918 b8e16776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16776 b8e16918
          have b8e17366 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e16937 x
               grind)
            | exact superpose b8e16937 b8e23
            | exact resolve b8e23 b8e16937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e17378 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e33 (σ X0) (σ X0)
               have i₂ := b8e16937 X0
               grind)
            | exact superpose b8e16937 b8e33
            | exact resolve b8e33 b8e16937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e17381 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e36 (σ X0) X1 (σ X0)
               have i₂ := b8e16937 X0
               grind)
            | exact superpose b8e16937 b8e36
            | exact resolve b8e36 b8e16937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e17427 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e246 (σ X0) (σ X0) X1
               have i₂ := b8e16937 X0
               grind)
            | exact superpose b8e16937 b8e246
            | exact resolve b8e246 b8e16937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e21029 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e60 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e60
            | (have j0 := b8e60 X0 X1
               grind)
            | exact resolve b8e60 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e21302 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e21029 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e21029
            | (have j0 := b8e21029 X1 X1
               grind)
            | exact resolve b8e21029 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21029
          have b8e31727 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b8e17381 (M.op X0 X0) (σ X0)
               have i₂ := b8e17378 X0
               grind)
            | exact superpose b8e17378 b8e17381
            | exact resolve b8e17381 b8e17378
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32026 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
            intro X0
            first
            | (have i₁ := b8e31727 X0
               have i₂ := b8e36 (M.op X0 X0) X0 X0
               grind)
            | (have i₁ := b8e31727 X0
               have i₂ := b8e36 X0 (M.op X0 X0) X0
               grind)
            | exact superpose b8e36 b8e31727
            | exact resolve b8e31727 b8e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31727
          have b8e32117 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
            intro X0
            first
            | (have i₁ := b8e32026 X0
               have i₂ := b8e17378 X0
               grind)
            | exact superpose b8e17378 b8e32026
            | exact resolve b8e32026 b8e17378
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32026
          have b8e36771 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))))) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e17427 X0 (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))))
               have i₂ := b8e32117 (M.op X0 X0)
               grind)
            | exact superpose b8e32117 b8e17427
            | exact resolve b8e17427 b8e32117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17427 b8e32117
          have b8e36891 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 (M.op X0 (M.op X0 X0)))))) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e36771 X0
               have i₂ := b8e5102 X0 (M.op X0 X0) (M.op X0 X0) (M.op X0 X0) X0
               grind)
            | (have i₁ := b8e36771 X0
               have i₂ := b8e5102 X0 (M.op X0 X0) (M.op X0 X0) X0 (M.op X0 X0)
               grind)
            | exact superpose b8e5102 b8e36771
            | exact resolve b8e36771 b8e5102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5102 b8e36771
          have b8e36965 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e36891 X0
               have i₂ := b8e477 (M.op X0 X0) X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b8e477 b8e36891
            | exact resolve b8e36891 b8e477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e477 b8e36891
          have b8e41976 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e591 X0 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e591
            | exact resolve b8e591 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e41986 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 X1
               have i₂ := b8e591 X0 X1
               grind)
            | exact superpose b8e591 b8e14
            | (have j1 := b8e591 X1 X1
               grind)
            | exact resolve b8e14 b8e591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e591
          have b8e42727 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e41986 X0 X1
               have i₂ := b8e16937 X0
               grind)
            | exact superpose b8e16937 b8e41986
            | (have j0 := b8e41986 X0 X1
               grind)
            | exact resolve b8e41986 b8e16937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41986
          have b8e42734 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e41976 X0 X1
               have i₂ := b8e16937 X1
               grind)
            | exact superpose b8e16937 b8e41976
            | (have j0 := b8e41976 X0 X1
               grind)
            | exact resolve b8e41976 b8e16937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41976
          have b8e43092 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e42727 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e42727
            | (have j0 := b8e42727 X0 X1
               grind)
            | exact resolve b8e42727 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42727
          have b8e43094 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e42734 X0 X1
               have i₂ := b8e25 X0 X1
               grind)
            | exact superpose b8e25 b8e42734
            | (have j0 := b8e42734 X0 X1
               grind)
            | exact resolve b8e42734 b8e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e42734
          have b8e43305 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e43092 X0 X1
               have i₂ := b8e16937 X1
               grind)
            | exact superpose b8e16937 b8e43092
            | (have j0 := b8e43092 X0 X1
               grind)
            | exact resolve b8e43092 b8e16937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43092
          have b8e166618 : ∀ X0 : G, (σ X0) = (M.op (σ (k x X0)) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e33 (σ x) (σ X0)
               have i₂ := b8e3380 X0
               grind)
            | exact superpose b8e3380 b8e33
            | (have j1 := b8e3380 X0
               grind)
            | exact resolve b8e33 b8e3380
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3380
          have b8e166788 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (k x X0)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e166618 X0
               have i₂ := b8e16937 X0
               grind)
            | exact superpose b8e16937 b8e166618
            | (have j0 := b8e166618 X0
               grind)
            | exact resolve b8e166618 b8e16937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e166618
          have b8e232698 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ (σ X0) = (M.op (σ (k x X0)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op X0 X0)
               have i₂ := b8e166788 X0
               grind)
            | exact superpose b8e166788 b8e14
            | (have j1 := b8e166788 X0
               grind)
            | exact resolve b8e14 b8e166788
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e166788
          have b8e232832 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ X0) = (M.op (σ (k x X0)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e232698 X0
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e232698
            | (have j0 := b8e232698 X0
               grind)
            | exact resolve b8e232698 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e232698
          have b8e319669 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e43094 X1 (τ X0)
               have i₂ := b8e16931 X0
               grind)
            | exact superpose b8e16931 b8e43094
            | (have j0 := b8e43094 X1 (τ X0)
               grind)
            | exact resolve b8e43094 b8e16931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16931 b8e43094
          have b8e319678 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e319669 X0 X1
               have i₂ := b8e15 (M.op X0 X0)
               grind)
            | exact superpose b8e15 b8e319669
            | (have j0 := b8e319669 X0 X1
               grind)
            | exact resolve b8e319669 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e319669
          have b8e319680 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e319678 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e319678
            | (have j0 := b8e319678 X0 X1
               grind)
            | exact resolve b8e319678 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e319678
          have b8e319710 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e17378 X0
               have i₂ := b8e319680 X1 X0
               grind)
            | exact superpose b8e319680 b8e17378
            | (have j1 := b8e319680 X1 X0
               grind)
            | exact resolve b8e17378 b8e319680
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e319680
          have b8e319732 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e319710 X0 X1
               have i₂ := b8e16937 X0
               grind)
            | exact superpose b8e16937 b8e319710
            | (have j0 := b8e319710 X0 X1
               grind)
            | exact resolve b8e319710 b8e16937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16937 b8e319710
          have b8e337342 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (M.op X0 X0)
               have i₂ := b8e43305 X1 X0
               grind)
            | exact superpose b8e43305 b8e14
            | (have j1 := b8e43305 X1 X0
               grind)
            | exact resolve b8e14 b8e43305
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43305
          have b8e337350 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e337342 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e337342
            | (have j0 := b8e337342 X0 X1
               grind)
            | exact resolve b8e337342 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e337342
          have b8e729517 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k x X0) = (M.op X0 x) ∨ (M.op X0 X0) = x := by
            intro X0
            first
            | (have i₁ := b8e17366
               have i₂ := b8e319732 x X0
               grind)
            | exact superpose b8e319732 b8e17366
            | (have j1 := b8e319732 x X0
               grind)
            | (have r₁ := b8e17366
               have r₂ := b8e319732 x x
               grind)
            | exact resolve b8e17366 b8e319732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17366 b8e319732
          have b8e729533 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ (M.op X0 X0) = x := by
            intro X0
            first
            | (have j0 := b8e729517 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e729517
          have b8e729579 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 x)) (σ x)) ∨ (M.op X0 X0) = x ∨ (M.op X0 X0) = x := by
            intro X0
            first
            | (have i₁ := b8e232832 X0
               have i₂ := b8e729533 X0
               grind)
            | exact superpose b8e729533 b8e232832
            | (have j0 := b8e232832 X0
               have j1 := b8e729533 X0
               grind)
            | exact resolve b8e232832 b8e729533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e232832
          have b8e729606 : ∀ X0 : G, (σ X0) = (M.op (σ x) (σ X0)) ∨ (k x X0) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b8e17378 X0
               have i₂ := b8e729533 X0
               grind)
            | exact superpose b8e729533 b8e17378
            | (have j1 := b8e729533 X0
               grind)
            | exact resolve b8e17378 b8e729533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17378 b8e729533
          have b8e729961 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 x)) (σ x)) ∨ (M.op X0 X0) = x := by
            intro X0
            first
            | (have j0 := b8e729579 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e729579
          have b8e730300 : (σ y) ≠ (σ y) ∨ (k x y) = (M.op y x) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e729606 y
               grind)
            | exact superpose b8e729606 b8e24
            | (have j1 := b8e729606 y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e729606 y
               grind)
            | exact resolve b8e24 b8e729606
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e729606
          have b8e730349 : (k x y) = (M.op y x) := by grind
          clear b8e730300
          have b8e730373 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 (σ (M.op y x))))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e3342 y X0
               have i₂ := b8e730349
               grind)
            | exact superpose b8e730349 b8e3342
            | (have j0 := b8e3342 y x
               grind)
            | exact resolve b8e3342 b8e730349
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3342
          have b8e730375 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e3348 y
               have i₂ := b8e730349
               grind)
            | exact superpose b8e730349 b8e3348
            | (have j0 := b8e3348 y
               grind)
            | exact resolve b8e3348 b8e730349
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3348 b8e730349
          have b8e730414 : (σ y) = (M.op (σ (M.op y x)) (σ x)) := by
            first
            | (have r₁ := b8e730375
               have r₂ := b8e24
               grind)
            | exact resolve b8e730375 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e730375
          have b8e730416 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 (σ (M.op y x))))) = X0 := by
            intro X0
            first
            | (have j0 := b8e730373 X0
               grind)
            | (have r₁ := b8e730373 X0
               have r₂ := b8e24
               grind)
            | exact resolve b8e730373 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e730373
          have b8e730472 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e33 (σ x) (σ (M.op y x))
               have i₂ := b8e730414
               grind)
            | exact superpose b8e730414 b8e33
            | exact resolve b8e33 b8e730414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e730520 : ∀ X0 : G, (M.op X0 (σ (M.op y x))) = (M.op (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b8e246 (σ (M.op y x)) (σ x) X0
               have i₂ := b8e730414
               grind)
            | exact superpose b8e730414 b8e246
            | exact resolve b8e246 b8e730414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e246 b8e730414
          have b8e731868 : (M.op (σ y) (σ (M.op y x))) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b8e17381 y (σ x)
               have i₂ := b8e730472
               grind)
            | exact superpose b8e730472 b8e17381
            | exact resolve b8e17381 b8e730472
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17381 b8e730472
          have b8e745306 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) X0) = X1 ∨ (σ X0) = (M.op (σ (M.op X0 x)) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e91 X0 X0 X1
               have i₂ := b8e729961 X0
               grind)
            | exact superpose b8e729961 b8e91
            | (have j1 := b8e729961 X0
               grind)
            | exact resolve b8e91 b8e729961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91 b8e729961
          have b8e795191 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ (M.op (M.op x X0) x)) (σ x)) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e33 (M.op x X0) (M.op x X0)
               have i₂ := b8e745306 (M.op x X0) X0
               grind)
            | exact superpose b8e745306 b8e33
            | (have j1 := b8e745306 (M.op x X0) x
               grind)
            | exact resolve b8e33 b8e745306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e745306
          have b8e804073 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e33 X1 X1
               have i₂ := b8e337350 X0 X1
               grind)
            | (have i₁ := b8e33 X0 X1
               have i₂ := b8e337350 (M.op X1 X0) X1
               grind)
            | exact superpose b8e337350 b8e33
            | (have j1 := b8e337350 X0 X0
               grind)
            | exact resolve b8e33 b8e337350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e337350
          have b8e804164 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e804073 y x
               grind)
            | exact superpose b8e804073 b8e20
            | (have j1 := b8e804073 y y
               grind)
            | exact resolve b8e20 b8e804073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e804073
          have b8e804172 : y = (M.op y y) ∨ x = (M.op y x) := by
            first
            | (have j1 := b8e21302 y y
               grind)
            | (have r₁ := b8e804164
               have r₂ := b8e21302 x y
               grind)
            | exact resolve b8e804164 b8e21302
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21302 b8e804164
          have b8e804182 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e16 y X0
               have i₂ := b8e804172
               grind)
            | exact superpose b8e804172 b8e16
            | (have j0 := b8e16 y X0
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e804172
               grind)
            | exact resolve b8e16 b8e804172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e804183 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e16907 y X0
               have i₂ := b8e804172
               grind)
            | exact superpose b8e804172 b8e16907
            | (have j0 := b8e16907 y X0
               grind)
            | exact resolve b8e16907 b8e804172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16907
          have b8e804525 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have j0 := b8e804183 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e804183
          have b8e804526 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have j0 := b8e804182 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e804182
          have b8e804693 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 y
               have i₂ := b8e804526 (τ X0)
               grind)
            | exact superpose b8e804526 b8e26
            | exact resolve b8e26 b8e804526
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e804526
          have b8e807106 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e804525 (σ X0)
               grind)
            | exact superpose b8e804525 b8e19
            | exact resolve b8e19 b8e804525
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e804525
          have b8e808320 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op y X0)) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e804693 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e804693
            | exact resolve b8e804693 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e804693
          have b8e808337 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e808320 X0
               have i₂ := b8e19 y X0
               grind)
            | exact superpose b8e19 b8e808320
            | exact resolve b8e808320 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e808320
          have b8e808777 : ∀ X0 : G, (σ y) = (M.op (σ (k y X0)) (σ X0)) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e33 (σ X0) (σ y)
               have i₂ := b8e807106 X0
               grind)
            | exact superpose b8e807106 b8e33
            | exact resolve b8e33 b8e807106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e807106
          have b8e809409 : ∀ X0 : G, (σ y) = (M.op (σ (M.op y X0)) (σ X0)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e808777 X0
               have i₂ := b8e808337 X0
               grind)
            | exact superpose b8e808337 b8e808777
            | exact resolve b8e808777 b8e808337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e808337 b8e808777
          have b8e809432 : ∀ X0 : G, (σ y) = (M.op (σ (M.op y X0)) (σ X0)) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have j0 := b8e809409 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e809409
          have b8e809613 : (M.op (σ x) (M.op (σ y) (σ y))) = (σ (M.op y (M.op y x))) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e730416 (σ (M.op y (M.op y x)))
               have i₂ := b8e809432 (M.op y x)
               grind)
            | exact superpose b8e809432 b8e730416
            | exact resolve b8e730416 b8e809432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e730416 b8e809432
          have b8e809632 : (M.op (σ x) (M.op (σ y) (σ y))) = (σ (M.op x (M.op y y))) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e809613
               have i₂ := b8e36 y x y
               grind)
            | (have i₁ := b8e809613
               have i₂ := b8e36 x y y
               grind)
            | exact superpose b8e36 b8e809613
            | exact resolve b8e809613 b8e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36 b8e809613
          have b8e809643 : (M.op (σ y) (σ (M.op y x))) = (σ (M.op x (M.op y y))) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e809632
               have i₂ := b8e730520 (σ y)
               grind)
            | exact superpose b8e730520 b8e809632
            | exact resolve b8e809632 b8e730520
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e730520 b8e809632
          have b8e809645 : (M.op (σ x) (σ (M.op y y))) = (σ (M.op x (M.op y y))) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e809643
               have i₂ := b8e731868
               grind)
            | exact superpose b8e731868 b8e809643
            | exact resolve b8e809643 b8e731868
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e731868 b8e809643
          have b8e858074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e809645
               have i₂ := b8e804172
               grind)
            | exact superpose b8e804172 b8e809645
            | exact resolve b8e809645 b8e804172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e804172 b8e809645
          have b8e858077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
          clear b8e858074
          have b8e858079 : x = (M.op y x) := by
            first
            | (have r₁ := b8e858077
               have r₂ := b8e20
               grind)
            | exact resolve b8e858077 b8e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e858077
          have b8e858306 : y = (M.op x x) := by
            first
            | (have i₁ := b8e33 x y
               have i₂ := b8e858079
               grind)
            | exact superpose b8e858079 b8e33
            | exact resolve b8e33 b8e858079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33 b8e858079
          have b8e860662 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (M.op x y) x)) (σ x)) := by
            first
            | (have i₁ := b8e36965 x
               have i₂ := b8e858306
               grind)
            | exact superpose b8e858306 b8e36965
            | exact resolve b8e36965 b8e858306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36965 b8e858306
          have b8e912711 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e795191 y
               have i₂ := b8e860662
               grind)
            | exact superpose b8e860662 b8e795191
            | (have j0 := b8e795191 y
               grind)
            | exact resolve b8e795191 b8e860662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e795191 b8e860662
          have b8e912713 : y = (M.op x y) := by
            first
            | (have r₁ := b8e912711
               have r₂ := b8e20
               grind)
            | exact resolve b8e912711 b8e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e912711
          have b8e912717 : False := by grind
          exact b8e912717

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_x_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
      · have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : (M.op x y) = (M.op x x) := by grind
        have b0e21 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e19
          | exact resolve b0e19 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e24 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
        have b0e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b0e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b0e18 X0 X0
             have i₂ := b0e57 (σ X0)
             grind)
          | exact superpose b0e57 b0e18
          | exact resolve b0e18 b0e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b0e65 X0
             have i₂ := b0e57 X0
             grind)
          | exact superpose b0e57 b0e65
          | exact resolve b0e65 b0e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e57 b0e65
        have b0e181 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e24
             have i₂ := b0e72 x
             grind)
          | exact superpose b0e72 b0e24
          | (have r₁ := b0e24
             have r₂ := b0e72 x
             grind)
          | exact resolve b0e24 b0e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24 b0e72
        have b0e189 : False := by grind
        exact b0e189
      · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
        · have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : (M.op x y) = (M.op x x) := by grind
          have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e20
            | exact resolve b1e20 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e28 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b1e26
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e26
            | exact resolve b1e26 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e26
          have b1e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b1e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b1e19 X0 X0
               have i₂ := b1e53 (σ X0)
               grind)
            | exact superpose b1e53 b1e19
            | exact resolve b1e19 b1e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b1e62 X0
               have i₂ := b1e53 X0
               grind)
            | exact superpose b1e53 b1e62
            | exact resolve b1e62 b1e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e53 b1e62
          have b1e195 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b1e28
               have i₂ := b1e67 x
               grind)
            | exact superpose b1e67 b1e28
            | (have r₁ := b1e28
               have r₂ := b1e67 x
               grind)
            | exact resolve b1e28 b1e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e28 b1e67
          have b1e203 : False := by grind
          exact b1e203
        · have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : (M.op x y) = (M.op x x) := by grind
          have b2e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e20
            | exact resolve b2e20 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e26 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b2e25
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e25
            | exact resolve b2e25 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e25
          have b2e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b2e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b2e19 X0 X0
               have i₂ := b2e48 (σ X0)
               grind)
            | exact superpose b2e48 b2e19
            | exact resolve b2e19 b2e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b2e54 X0
               have i₂ := b2e48 X0
               grind)
            | exact superpose b2e48 b2e54
            | exact resolve b2e54 b2e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e48 b2e54
          have b2e209 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b2e26
               have i₂ := b2e59 x
               grind)
            | exact superpose b2e59 b2e26
            | (have r₁ := b2e26
               have r₂ := b2e59 x
               grind)
            | exact resolve b2e26 b2e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e26 b2e59
          have b2e218 : False := by grind
          exact b2e218
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b3e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : (M.op x y) = (M.op x x) := by grind
          have b3e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b3e23 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          have b3e24 : (M.op y y) = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e33 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op y x) y))) := by
            intro X0
            first
            | (have i₁ := b3e13 y X0 y
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e66 : (M.op x x) ≠ (M.op x x) ∨ (M.op y x) = (k x y) := by
            first
            | (have i₁ := b3e16 x y
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e16
            | (have j0 := b3e16 x x
               grind)
            | (have r₁ := b3e16 x y
               have r₂ := b3e21
               grind)
            | exact resolve b3e16 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e71 : (M.op y x) = (k x y) := by grind
          clear b3e66
          have b3e92 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b3e17 (σ x) (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e17
            | (have j0 := b3e17 (σ x) (σ y)
               grind)
            | (have r₁ := b3e17 (σ x) (σ y)
               have r₂ := b3e23
               grind)
            | exact resolve b3e17 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e94 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b3e92
          have b3e95 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e94
               have r₂ := b3e22
               grind)
            | exact resolve b3e94 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e94
          have b3e96 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b3e95
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e95
            | exact resolve b3e95 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e95
          have b3e97 : (σ x) = (σ (M.op y x)) := by
            first
            | (have i₁ := b3e96
               have i₂ := b3e71
               grind)
            | exact superpose b3e71 b3e96
            | exact resolve b3e96 b3e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e71 b3e96
          have b3e159 : (M.op y x) = (τ (σ x)) := by
            first
            | (have i₁ := b3e14 (M.op y x)
               have i₂ := b3e97
               grind)
            | exact superpose b3e97 b3e14
            | exact resolve b3e14 b3e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e97
          have b3e160 : x = (M.op y x) := by
            first
            | (have i₁ := b3e159
               have i₂ := b3e14 x
               grind)
            | exact superpose b3e14 b3e159
            | exact resolve b3e159 b3e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e159
          have b3e175 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b3e13 x X0 y
               have i₂ := b3e160
               grind)
            | exact superpose b3e160 b3e13
            | exact resolve b3e13 b3e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e176 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b3e33 X0
               have i₂ := b3e160
               grind)
            | exact superpose b3e160 b3e33
            | exact resolve b3e33 b3e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e33 b3e160
          have b3e189 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b3e176 X0
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e176
            | exact resolve b3e176 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e176
          have b3e195 : x = y := by
            first
            | (have i₁ := b3e189 x
               have i₂ := b3e175 x
               grind)
            | exact superpose b3e175 b3e189
            | exact resolve b3e189 b3e175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e175 b3e189
          have b3e202 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e195
               grind)
            | exact superpose b3e195 b3e22
            | exact resolve b3e22 b3e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e195
          have b3e209 : False := by grind
          exact b3e209
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b4e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : (M.op x y) = (M.op x x) := by grind
            have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
            have b4e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
            have b4e25 : (M.op y y) ≠ (M.op y x) := by grind
            have b4e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : (M.op x y) ≠ (M.op y x) := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e25
              | exact resolve b4e25 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e29 : (M.op x x) ≠ (M.op y x) := by
              first
              | (have i₁ := b4e27
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e27
              | exact resolve b4e27 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e27
            have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b4e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b4e14 X0 X2 X3
                 grind)
              | exact superpose b4e14 b4e14
              | exact resolve b4e14 b4e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e58 : (M.op x x) ≠ (M.op x x) ∨ (M.op y x) = (k x y) := by
              first
              | (have i₁ := b4e17 x y
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e17
              | (have j0 := b4e17 x x
                 grind)
              | (have r₁ := b4e17 x y
                 have r₂ := b4e22
                 grind)
              | exact resolve b4e17 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e63 : (M.op y x) = (k x y) := by grind
            clear b4e58
            have b4e81 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b4e18 (σ x) (σ y)
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e18
              | (have j0 := b4e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b4e18 (σ x) (σ y)
                 have r₂ := b4e24
                 grind)
              | exact resolve b4e18 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e83 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b4e81
            have b4e84 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e83
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e83 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e83
            have b4e86 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b4e84
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e84
              | exact resolve b4e84 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e84
            have b4e88 : (σ x) = (σ (M.op y x)) := by
              first
              | (have i₁ := b4e86
                 have i₂ := b4e63
                 grind)
              | exact superpose b4e63 b4e86
              | exact resolve b4e86 b4e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e63 b4e86
            have b4e146 : (M.op y x) = (τ (σ x)) := by
              first
              | (have i₁ := b4e15 (M.op y x)
                 have i₂ := b4e88
                 grind)
              | exact superpose b4e88 b4e15
              | exact resolve b4e15 b4e88
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e88
            have b4e147 : x = (M.op y x) := by
              first
              | (have i₁ := b4e146
                 have i₂ := b4e15 x
                 grind)
              | exact superpose b4e15 b4e146
              | exact resolve b4e146 b4e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e146
            have b4e160 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b4e29
                 have i₂ := b4e147
                 grind)
              | exact superpose b4e147 b4e29
              | exact resolve b4e29 b4e147
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e29
            have b4e396 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b4e34 X0 X2 X0 X1
                 have i₂ := b4e14 X0 X0 X1
                 grind)
              | exact superpose b4e14 b4e34
              | exact resolve b4e34 b4e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e34
            have b4e846 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b4e14 X1 X1 x
                 have i₂ := b4e396 X1 x X0
                 grind)
              | exact superpose b4e396 b4e14
              | exact resolve b4e14 b4e396
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e396
            have b4e969 : x = (M.op x (M.op y x)) := by
              first
              | (have i₁ := b4e846 y x
                 have i₂ := b4e147
                 grind)
              | exact superpose b4e147 b4e846
              | exact resolve b4e846 b4e147
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e846
            have b4e1007 : x = (M.op x x) := by
              first
              | (have i₁ := b4e969
                 have i₂ := b4e147
                 grind)
              | exact superpose b4e147 b4e969
              | exact resolve b4e969 b4e147
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e147 b4e969
            have b4e1014 : False := by grind
            exact b4e1014
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : (M.op x y) = (M.op x x) := by grind
            have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
            have b5e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
            have b5e26 : (M.op x y) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e30 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op x x) y))) := by
              intro X0
              first
              | (have i₁ := b5e14 y X0 x
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b5e14 X0 X2 X3
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e54 : (M.op x x) ≠ (M.op x x) ∨ (M.op y x) = (k x y) := by
              first
              | (have i₁ := b5e17 x y
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e17
              | (have j0 := b5e17 x x
                 grind)
              | (have r₁ := b5e17 x y
                 have r₂ := b5e22
                 grind)
              | exact resolve b5e17 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e57 : (M.op y x) = (k x y) := by grind
            clear b5e54
            have b5e72 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b5e18 (σ x) (σ y)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e18
              | (have j0 := b5e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b5e18 (σ x) (σ y)
                 have r₂ := b5e24
                 grind)
              | exact resolve b5e18 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e74 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b5e72
            have b5e75 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e74
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e74 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e74
            have b5e76 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b5e75
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e75
              | exact resolve b5e75 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e75
            have b5e77 : (σ x) = (σ (M.op y x)) := by
              first
              | (have i₁ := b5e76
                 have i₂ := b5e57
                 grind)
              | exact superpose b5e57 b5e76
              | exact resolve b5e76 b5e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e57 b5e76
            have b5e135 : (M.op y x) = (τ (σ x)) := by
              first
              | (have i₁ := b5e15 (M.op y x)
                 have i₂ := b5e77
                 grind)
              | exact superpose b5e77 b5e15
              | exact resolve b5e15 b5e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e77
            have b5e136 : x = (M.op y x) := by
              first
              | (have i₁ := b5e135
                 have i₂ := b5e15 x
                 grind)
              | exact superpose b5e15 b5e135
              | exact resolve b5e135 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e135
            have b5e150 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op x x))) := by
              intro X0
              first
              | (have i₁ := b5e14 x X0 y
                 have i₂ := b5e136
                 grind)
              | exact superpose b5e136 b5e14
              | exact resolve b5e14 b5e136
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e356 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e31 X0 X2 X0 X1
                 have i₂ := b5e14 X0 X0 X1
                 grind)
              | exact superpose b5e14 b5e31
              | exact resolve b5e31 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e31
            have b5e872 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X1 X1 x
                 have i₂ := b5e356 X1 x X0
                 grind)
              | exact superpose b5e356 b5e14
              | exact resolve b5e14 b5e356
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e356
            have b5e1035 : x = (M.op x (M.op y x)) := by
              first
              | (have i₁ := b5e872 y x
                 have i₂ := b5e136
                 grind)
              | exact superpose b5e136 b5e872
              | exact resolve b5e872 b5e136
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e872
            have b5e1072 : x = (M.op x x) := by
              first
              | (have i₁ := b5e1035
                 have i₂ := b5e136
                 grind)
              | exact superpose b5e136 b5e1035
              | exact resolve b5e1035 b5e136
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e136 b5e1035
            have b5e1176 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
              intro X0
              first
              | (have i₁ := b5e30 X0
                 have i₂ := b5e1072
                 grind)
              | exact superpose b5e1072 b5e30
              | exact resolve b5e30 b5e1072
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e30 b5e1072
            have b5e1210 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x x))) := by
              intro X0
              first
              | (have i₁ := b5e1176 X0
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e1176
              | exact resolve b5e1176 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1176
            have b5e1211 : x = y := by
              first
              | (have i₁ := b5e1210 x
                 have i₂ := b5e150 x
                 grind)
              | exact superpose b5e150 b5e1210
              | exact resolve b5e1210 b5e150
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e150 b5e1210
            have b5e1559 : (M.op x x) ≠ (M.op x x) := by
              first
              | (have i₁ := b5e26
                 have i₂ := b5e1211
                 grind)
              | exact superpose b5e1211 b5e26
              | exact resolve b5e26 b5e1211
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1211
            have b5e1566 : False := by grind
            exact b5e1566
      · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b6e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b6e24 : (M.op y y) = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e33 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op y x) y))) := by
            intro X0
            first
            | (have i₁ := b6e13 y X0 y
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e13 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
               have i₂ := b6e13 X0 X2 X3
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e35 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e13 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
               have i₂ := b6e13 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e512 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e34 X0 X2 X0 X1
               have i₂ := b6e13 X0 X0 X1
               grind)
            | exact superpose b6e13 b6e34
            | exact resolve b6e34 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e34
          have b6e568 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b6e13 X1 X1 x
               have i₂ := b6e512 X1 x X0
               grind)
            | exact superpose b6e512 b6e13
            | exact resolve b6e13 b6e512
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e636 : y = (M.op y (M.op y (M.op y x))) := by
            first
            | (have i₁ := b6e568 y y
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e568
            | exact resolve b6e568 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e651 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e35 (M.op X0 (M.op X0 X1)) X1 X1
               have i₂ := b6e568 X0 X1
               grind)
            | exact superpose b6e568 b6e35
            | exact resolve b6e35 b6e568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e655 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e651 X1 X0 X2
               have i₂ := b6e568 X0 X1
               grind)
            | exact superpose b6e568 b6e651
            | exact resolve b6e651 b6e568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e651
          have b6e746 : (M.op y x) = (M.op (M.op y x) y) := by
            first
            | (have i₁ := b6e568 y (M.op y x)
               have i₂ := b6e636
               grind)
            | exact superpose b6e636 b6e568
            | exact resolve b6e568 b6e636
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e568 b6e636
          have b6e1063 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op y x))) := by
            intro X0
            first
            | (have i₁ := b6e33 X0
               have i₂ := b6e746
               grind)
            | exact superpose b6e746 b6e33
            | exact resolve b6e33 b6e746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e33 b6e746
          have b6e1315 : ∀ X0 : G, y = (M.op (M.op y x) (M.op (M.op X0 (M.op y x)) (M.op y x))) := by
            intro X0
            first
            | (have i₁ := b6e512 (M.op y x) X0 x
               have i₂ := b6e1063 x
               grind)
            | exact superpose b6e1063 b6e512
            | exact resolve b6e512 b6e1063
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e512
          have b6e1318 : ∀ X0 : G, (M.op y (M.op y x)) = (M.op (M.op X0 (M.op y x)) (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b6e35 (M.op y x) (M.op X0 (M.op y x)) X0
               have i₂ := b6e1063 (M.op X0 (M.op y x))
               grind)
            | exact superpose b6e1063 b6e35
            | exact resolve b6e35 b6e1063
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e35 b6e1063
          have b6e1336 : y = (M.op (M.op y x) (M.op y (M.op y x))) := by
            first
            | (have i₁ := b6e1315 x
               have i₂ := b6e1318 x
               grind)
            | exact superpose b6e1318 b6e1315
            | exact resolve b6e1315 b6e1318
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1315 b6e1318
          have b6e1341 : x = y := by
            first
            | (have i₁ := b6e1336
               have i₂ := b6e655 x y y
               grind)
            | exact superpose b6e655 b6e1336
            | exact resolve b6e1336 b6e655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e655 b6e1336
          have b6e1581 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e1341
               grind)
            | exact superpose b6e1341 b6e23
            | exact resolve b6e23 b6e1341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1341
          have b6e1593 : False := by grind
          exact b6e1593
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b7e22 : (M.op x y) = (M.op x x) := by grind
            have b7e25 : (M.op y y) ≠ (M.op y x) := by grind
            have b7e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e27 : (M.op x y) ≠ (M.op y x) := by
              first
              | (have i₁ := b7e25
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e25
              | exact resolve b7e25 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e29 : (M.op x x) ≠ (M.op y x) := by
              first
              | (have i₁ := b7e27
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e27
              | exact resolve b7e27 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e27
            have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b7e14 X0 X2 X3
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e427 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e34 X0 X2 X0 X1
                 have i₂ := b7e14 X0 X0 X1
                 grind)
              | exact superpose b7e14 b7e34
              | exact resolve b7e34 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e34
            have b7e477 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X1 X1 x
                 have i₂ := b7e427 X1 x X0
                 grind)
              | exact superpose b7e427 b7e14
              | exact resolve b7e14 b7e427
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e427
            have b7e530 : y = (M.op y (M.op y (M.op x y))) := by
              first
              | (have i₁ := b7e477 y y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e477
              | exact resolve b7e477 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e534 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
              intro X0
              first
              | (have i₁ := b7e477 X0 (M.op X0 X0)
                 have i₂ := b7e477 X0 X0
                 grind)
              | exact superpose b7e477 b7e477
              | exact resolve b7e477 b7e477
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e477
            have b7e549 : y = (M.op y (M.op y (M.op x x))) := by
              first
              | (have i₁ := b7e530
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e530
              | exact resolve b7e530 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e530
            have b7e647 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X0 X1 X0
                 have i₂ := b7e534 X0
                 grind)
              | exact superpose b7e534 b7e14
              | exact resolve b7e14 b7e534
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e534
            have b7e956 : x = y := by
              first
              | (have i₁ := b7e549
                 have i₂ := b7e647 x y
                 grind)
              | exact superpose b7e647 b7e549
              | exact resolve b7e549 b7e647
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e549 b7e647
            have b7e1048 : (M.op x x) ≠ (M.op x x) := by
              first
              | (have i₁ := b7e29
                 have i₂ := b7e956
                 grind)
              | exact superpose b7e956 b7e29
              | exact resolve b7e29 b7e956
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e29 b7e956
            have b7e1056 : False := by grind
            exact b7e1056
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b8e22 : (M.op x y) = (M.op x x) := by grind
            have b8e26 : (M.op x y) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b8e14 X0 X2 X3
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e383 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e31 X0 X2 X0 X1
                 have i₂ := b8e14 X0 X0 X1
                 grind)
              | exact superpose b8e14 b8e31
              | exact resolve b8e31 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e31
            have b8e428 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b8e383 X1 x X3
                 have i₂ := b8e383 X1 x X0
                 grind)
              | exact superpose b8e383 b8e383
              | exact resolve b8e383 b8e383
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e439 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X1 X1 x
                 have i₂ := b8e383 X1 x X0
                 grind)
              | exact superpose b8e383 b8e14
              | exact resolve b8e14 b8e383
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e383
            have b8e495 : y = (M.op y (M.op x (M.op x x))) := by
              first
              | (have i₁ := b8e439 x y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e439
              | exact resolve b8e439 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e499 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
              intro X0
              first
              | (have i₁ := b8e439 X0 (M.op X0 X0)
                 have i₂ := b8e439 X0 X0
                 grind)
              | exact superpose b8e439 b8e439
              | exact resolve b8e439 b8e439
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e439
            have b8e761 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X0 X1 X0
                 have i₂ := b8e499 X0
                 grind)
              | exact superpose b8e499 b8e14
              | exact resolve b8e14 b8e499
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e499
            have b8e926 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x x)))) := by
              intro X0
              first
              | (have i₁ := b8e428 y (M.op x (M.op x x)) X0
                 have i₂ := b8e495
                 grind)
              | exact superpose b8e495 b8e428
              | exact resolve b8e428 b8e495
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e495
            have b8e942 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e428 X1 (M.op X2 (M.op X0 X0)) X2
                 have i₂ := b8e761 X0 X2
                 grind)
              | exact superpose b8e761 b8e428
              | exact resolve b8e428 b8e761
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e428 b8e761
            have b8e1039 : (M.op x x) = (M.op y y) := by
              first
              | (have i₁ := b8e926 x
                 have i₂ := b8e942 x x x
                 grind)
              | exact superpose b8e942 b8e926
              | exact resolve b8e926 b8e942
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e926 b8e942
            have b8e1098 : (M.op x y) ≠ (M.op x x) := by
              first
              | (have i₁ := b8e26
                 have i₂ := b8e1039
                 grind)
              | exact superpose b8e1039 b8e26
              | exact resolve b8e26 b8e1039
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1039
            have b8e1135 : False := by grind
            exact b8e1135
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b9e22 : (M.op x x) = (M.op y x) := by grind
          have b9e23 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          have b9e24 : (M.op y x) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e20
            | exact resolve b9e20 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b9e13 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
               have i₂ := b9e13 X0 X2 X3
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e46 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b9e16 y X0
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e16
            | (have j0 := b9e16 y X0
               grind)
            | (have r₁ := b9e16 y x
               have r₂ := b9e24
               grind)
            | exact resolve b9e16 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e49 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b9e16 (σ x) (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 (σ x) (σ x)
               grind)
            | (have r₁ := b9e16 (σ x) (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b9e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e51 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          clear b9e49
          have b9e53 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b9e51
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e51
            | exact resolve b9e51 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e51
          have b9e55 : ∀ X0 : G, (M.op x x) ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b9e46 X0
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e46
            | (have j0 := b9e46 X0
               grind)
            | exact resolve b9e46 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e46
          have b9e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b9e19 X0 X0
               have i₂ := b9e50 (σ X0)
               grind)
            | exact superpose b9e50 b9e19
            | exact resolve b9e19 b9e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b9e57 X0
               have i₂ := b9e50 X0
               grind)
            | exact superpose b9e50 b9e57
            | exact resolve b9e57 b9e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e50 b9e57
          have b9e67 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (k x y) := by
            first
            | (have i₁ := b9e17 x y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e17
            | (have j0 := b9e17 x y
               grind)
            | (have r₁ := b9e17 x y
               have r₂ := b9e22
               grind)
            | exact resolve b9e17 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e69 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by grind
          clear b9e67
          have b9e70 : x = (k x y) := by
            first
            | (have r₁ := b9e69
               have r₂ := b9e21
               grind)
            | exact resolve b9e69 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e69
          have b9e106 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b9e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b9e106 X0 X1
               have j1 := b9e16 X0 X1
               grind)
            | (have r₁ := b9e106 X0 X1
               have r₂ := b9e16 X0 X1
               grind)
            | (have r₁ := b9e106 X1 X1
               have r₂ := b9e16 X1 X1
               grind)
            | exact resolve b9e106 b9e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e106
          have b9e185 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b9e55 x
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e55
            | (have j0 := b9e55 x
               grind)
            | (have r₁ := b9e55 x
               have r₂ := b9e22
               grind)
            | exact resolve b9e55 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e55
          have b9e190 : (M.op x y) = (k y x) := by grind
          clear b9e185
          have b9e256 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b9e113 (σ y) (σ x)
               have i₂ := b9e53
               grind)
            | exact superpose b9e53 b9e113
            | (have j0 := b9e113 (σ y) (σ x)
               grind)
            | exact resolve b9e113 b9e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e113
          have b9e285 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b9e256
               have i₂ := b9e70
               grind)
            | exact superpose b9e70 b9e256
            | exact resolve b9e256 b9e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e256
          have b9e290 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b9e285
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e285
            | exact resolve b9e285 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e285
          have b9e292 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b9e290
               have i₂ := b9e62 x
               grind)
            | exact superpose b9e62 b9e290
            | exact resolve b9e290 b9e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e290
          have b9e293 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b9e292
               have i₂ := b9e19 y x
               grind)
            | exact superpose b9e19 b9e292
            | exact resolve b9e292 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e292
          have b9e294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b9e293
               have i₂ := b9e190
               grind)
            | exact superpose b9e190 b9e293
            | exact resolve b9e293 b9e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e190 b9e293
          have b9e295 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b9e294
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e294
            | exact resolve b9e294 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e294
          have b9e296 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have r₁ := b9e295
               have r₂ := b9e25
               grind)
            | exact resolve b9e295 b9e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e25 b9e295
          have b9e483 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b9e30 X0 X2 X0 X1
               have i₂ := b9e13 X0 X0 X1
               grind)
            | exact superpose b9e13 b9e30
            | exact resolve b9e30 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e30
          have b9e625 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X1 X1 x
               have i₂ := b9e483 X1 x X0
               grind)
            | exact superpose b9e483 b9e13
            | exact resolve b9e13 b9e483
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e483
          have b9e754 : (σ x) = (M.op (σ x) (M.op (σ y) (σ (k x y)))) := by
            first
            | (have i₁ := b9e625 (σ y) (σ x)
               have i₂ := b9e53
               grind)
            | exact superpose b9e53 b9e625
            | exact resolve b9e625 b9e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e625
          have b9e783 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b9e754
               have i₂ := b9e70
               grind)
            | exact superpose b9e70 b9e754
            | exact resolve b9e754 b9e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e754
          have b9e790 : (σ x) = (M.op (σ x) (σ (k x y))) := by
            first
            | (have i₁ := b9e783
               have i₂ := b9e53
               grind)
            | exact superpose b9e53 b9e783
            | exact resolve b9e783 b9e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e53 b9e783
          have b9e791 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e790
               have i₂ := b9e70
               grind)
            | exact superpose b9e70 b9e790
            | exact resolve b9e790 b9e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e70 b9e790
          have b9e792 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b9e791
               have i₂ := b9e62 x
               grind)
            | exact superpose b9e62 b9e791
            | exact resolve b9e791 b9e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e62 b9e791
          have b9e793 : False := by grind
          exact b9e793
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b10e22 : (M.op x y) ≠ (M.op x x) := by grind
            have b10e23 : (M.op x x) = (M.op y x) := by grind
            have b10e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            have b10e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b10e21
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e21
              | exact resolve b10e21 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b10e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b10e14 X0 X2 X3
                 grind)
              | exact superpose b10e14 b10e14
              | exact resolve b10e14 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e40 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ x)) (σ y)))) := by
              intro X0
              first
              | (have i₁ := b10e14 (σ y) X0 (σ x)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e14
              | exact resolve b10e14 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 (σ x) (σ x)
                 grind)
              | (have r₁ := b10e17 (σ x) (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b10e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e54 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
            clear b10e52
            have b10e56 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b10e54
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e54
              | exact resolve b10e54 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e54
            have b10e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b10e20 X0 X0
                 have i₂ := b10e53 (σ X0)
                 grind)
              | exact superpose b10e53 b10e20
              | exact resolve b10e20 b10e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b10e59 X0
                 have i₂ := b10e53 X0
                 grind)
              | exact superpose b10e53 b10e59
              | exact resolve b10e59 b10e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e53 b10e59
            have b10e69 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (k x y) := by
              first
              | (have i₁ := b10e18 x y
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e18
              | (have j0 := b10e18 x y
                 grind)
              | (have r₁ := b10e18 x y
                 have r₂ := b10e23
                 grind)
              | exact resolve b10e18 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e71 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by grind
            clear b10e69
            have b10e72 : x = (k x y) := by
              first
              | (have r₁ := b10e71
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e71 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e71
            have b10e465 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e34 X0 X2 X0 X1
                 have i₂ := b10e14 X0 X0 X1
                 grind)
              | exact superpose b10e14 b10e34
              | exact resolve b10e34 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e34
            have b10e602 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b10e14 X1 X1 x
                 have i₂ := b10e465 X1 x X0
                 grind)
              | exact superpose b10e465 b10e14
              | exact resolve b10e14 b10e465
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e465
            have b10e722 : (σ x) = (M.op (σ x) (M.op (σ y) (σ (k x y)))) := by
              first
              | (have i₁ := b10e602 (σ y) (σ x)
                 have i₂ := b10e56
                 grind)
              | exact superpose b10e56 b10e602
              | exact resolve b10e602 b10e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e732 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
              intro X0
              first
              | (have i₁ := b10e602 X0 (M.op X0 X0)
                 have i₂ := b10e602 X0 X0
                 grind)
              | exact superpose b10e602 b10e602
              | exact resolve b10e602 b10e602
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e749 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
              first
              | (have i₁ := b10e722
                 have i₂ := b10e72
                 grind)
              | exact superpose b10e72 b10e722
              | exact resolve b10e722 b10e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e722
            have b10e756 : (σ x) = (M.op (σ x) (σ (k x y))) := by
              first
              | (have i₁ := b10e749
                 have i₂ := b10e56
                 grind)
              | exact superpose b10e56 b10e749
              | exact resolve b10e749 b10e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e56 b10e749
            have b10e757 : (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b10e756
                 have i₂ := b10e72
                 grind)
              | exact superpose b10e72 b10e756
              | exact resolve b10e756 b10e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e72 b10e756
            have b10e758 : (σ x) = (σ (M.op x x)) := by
              first
              | (have i₁ := b10e757
                 have i₂ := b10e64 x
                 grind)
              | exact superpose b10e64 b10e757
              | exact resolve b10e757 b10e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e757
            have b10e1113 : (M.op x x) = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 (M.op x x)
                 have i₂ := b10e758
                 grind)
              | exact superpose b10e758 b10e15
              | exact resolve b10e15 b10e758
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e1114 : x = (M.op x x) := by
              first
              | (have i₁ := b10e1113
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e1113
              | exact resolve b10e1113 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e1113
            have b10e1136 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op x x))) := by
              intro X0
              first
              | (have i₁ := b10e14 x X0 x
                 have i₂ := b10e1114
                 grind)
              | exact superpose b10e1114 b10e14
              | exact resolve b10e14 b10e1114
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e1160 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b10e1136 X0
                 have i₂ := b10e1114
                 grind)
              | exact superpose b10e1114 b10e1136
              | exact resolve b10e1136 b10e1114
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e1114 b10e1136
            have b10e1409 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b10e602 X0 (M.op X0 x)
                 have i₂ := b10e1160 X0
                 grind)
              | exact superpose b10e1160 b10e602
              | exact resolve b10e602 b10e1160
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e602 b10e1160
            have b10e2693 : (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y))) (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y)))) := by
              first
              | (have i₁ := b10e40 (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y)))
                 have i₂ := b10e732 (M.op (M.op (σ x) (σ x)) (σ y))
                 grind)
              | exact superpose b10e732 b10e40
              | exact resolve b10e40 b10e732
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e40 b10e732
            have b10e2707 : (σ y) = (M.op (M.op (M.op (σ (M.op x x)) (σ y)) (M.op (σ (M.op x x)) (σ y))) (M.op (M.op (σ (M.op x x)) (σ y)) (M.op (σ (M.op x x)) (σ y)))) := by
              first
              | (have i₁ := b10e2693
                 have i₂ := b10e64 x
                 grind)
              | exact superpose b10e64 b10e2693
              | exact resolve b10e2693 b10e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e2693
            have b10e2716 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
              first
              | (have i₁ := b10e2707
                 have i₂ := b10e758
                 grind)
              | exact superpose b10e758 b10e2707
              | exact resolve b10e2707 b10e758
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e2707
            have b10e2720 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
              first
              | (have i₁ := b10e2716
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e2716
              | exact resolve b10e2716 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e2716
            have b10e2722 : (σ y) = (M.op (M.op (σ (M.op x x)) (σ (M.op x x))) (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
              first
              | (have i₁ := b10e2720
                 have i₂ := b10e64 x
                 grind)
              | exact superpose b10e64 b10e2720
              | exact resolve b10e2720 b10e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e2720
            have b10e2723 : (σ y) = (M.op (σ (M.op (M.op x x) (M.op x x))) (σ (M.op (M.op x x) (M.op x x)))) := by
              first
              | (have i₁ := b10e2722
                 have i₂ := b10e64 (M.op x x)
                 grind)
              | exact superpose b10e64 b10e2722
              | exact resolve b10e2722 b10e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e2722
            have b10e2724 : (σ y) = (σ (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) (M.op x x)))) := by
              first
              | (have i₁ := b10e2723
                 have i₂ := b10e64 (M.op (M.op x x) (M.op x x))
                 grind)
              | exact superpose b10e64 b10e2723
              | exact resolve b10e2723 b10e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e2723
            have b10e2725 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) := by
              first
              | (have i₁ := b10e2724
                 have i₂ := b10e1409 x
                 grind)
              | exact superpose b10e1409 b10e2724
              | exact resolve b10e2724 b10e1409
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e2724
            have b10e2726 : (σ y) = (σ (M.op x x)) := by
              first
              | (have i₁ := b10e2725
                 have i₂ := b10e1409 x
                 grind)
              | exact superpose b10e1409 b10e2725
              | exact resolve b10e2725 b10e1409
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e1409 b10e2725
            have b10e2727 : (σ x) = (σ y) := by
              first
              | (have i₁ := b10e2726
                 have i₂ := b10e758
                 grind)
              | exact superpose b10e758 b10e2726
              | exact resolve b10e2726 b10e758
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e758 b10e2726
            have b10e2740 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b10e64 y
                 have i₂ := b10e2727
                 grind)
              | exact superpose b10e2727 b10e64
              | exact resolve b10e64 b10e2727
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e64 b10e2727
            have b10e2750 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b10e2740
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e2740
              | exact resolve b10e2740 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e2740
            have b10e2760 : False := by grind
            exact b10e2760
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b11e22 : (M.op x y) ≠ (M.op x x) := by grind
            have b11e23 : (M.op x x) = (M.op y x) := by grind
            have b11e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b11e21
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e21
              | exact resolve b11e21 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b11e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b11e14 X0 X2 X3
                 grind)
              | exact superpose b11e14 b11e14
              | exact resolve b11e14 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e45 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ x)) (σ y)))) := by
              intro X0
              first
              | (have i₁ := b11e14 (σ y) X0 (σ x)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e14
              | exact resolve b11e14 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e55 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 (σ x) (σ x)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b11e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e57 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
            clear b11e55
            have b11e58 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b11e57
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e57
              | exact resolve b11e57 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e57
            have b11e60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b11e20 X0 X0
                 have i₂ := b11e56 (σ X0)
                 grind)
              | exact superpose b11e56 b11e20
              | exact resolve b11e20 b11e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b11e60 X0
                 have i₂ := b11e56 X0
                 grind)
              | exact superpose b11e56 b11e60
              | exact resolve b11e60 b11e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e56 b11e60
            have b11e73 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (k x y) := by
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
            have b11e75 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by grind
            clear b11e73
            have b11e76 : x = (k x y) := by
              first
              | (have r₁ := b11e75
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e75 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e75
            have b11e206 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b11e27
                 have i₂ := b11e67 x
                 grind)
              | exact superpose b11e67 b11e27
              | exact resolve b11e27 b11e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e27
            have b11e426 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e35 X0 X2 X0 X1
                 have i₂ := b11e14 X0 X0 X1
                 grind)
              | exact superpose b11e14 b11e35
              | exact resolve b11e35 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e35
            have b11e558 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X1 X1 x
                 have i₂ := b11e426 X1 x X0
                 grind)
              | exact superpose b11e426 b11e14
              | exact resolve b11e14 b11e426
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e426
            have b11e671 : (σ x) = (M.op (σ x) (M.op (σ y) (σ (k x y)))) := by
              first
              | (have i₁ := b11e558 (σ y) (σ x)
                 have i₂ := b11e58
                 grind)
              | exact superpose b11e58 b11e558
              | exact resolve b11e558 b11e58
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e680 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
              intro X0
              first
              | (have i₁ := b11e558 X0 (M.op X0 X0)
                 have i₂ := b11e558 X0 X0
                 grind)
              | exact superpose b11e558 b11e558
              | exact resolve b11e558 b11e558
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e696 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
              first
              | (have i₁ := b11e671
                 have i₂ := b11e76
                 grind)
              | exact superpose b11e76 b11e671
              | exact resolve b11e671 b11e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e671
            have b11e703 : (σ x) = (M.op (σ x) (σ (k x y))) := by
              first
              | (have i₁ := b11e696
                 have i₂ := b11e58
                 grind)
              | exact superpose b11e58 b11e696
              | exact resolve b11e696 b11e58
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e58 b11e696
            have b11e704 : (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b11e703
                 have i₂ := b11e76
                 grind)
              | exact superpose b11e76 b11e703
              | exact resolve b11e703 b11e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e76 b11e703
            have b11e705 : (σ x) = (σ (M.op x x)) := by
              first
              | (have i₁ := b11e704
                 have i₂ := b11e67 x
                 grind)
              | exact superpose b11e67 b11e704
              | exact resolve b11e704 b11e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e704
            have b11e1050 : (M.op x x) = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 (M.op x x)
                 have i₂ := b11e705
                 grind)
              | exact superpose b11e705 b11e15
              | exact resolve b11e15 b11e705
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e1051 : x = (M.op x x) := by
              first
              | (have i₁ := b11e1050
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e1050
              | exact resolve b11e1050 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1050
            have b11e1072 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op x x))) := by
              intro X0
              first
              | (have i₁ := b11e14 x X0 x
                 have i₂ := b11e1051
                 grind)
              | exact superpose b11e1051 b11e14
              | exact resolve b11e14 b11e1051
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e1096 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b11e1072 X0
                 have i₂ := b11e1051
                 grind)
              | exact superpose b11e1051 b11e1072
              | exact resolve b11e1072 b11e1051
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1051 b11e1072
            have b11e1340 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b11e558 X0 (M.op X0 x)
                 have i₂ := b11e1096 X0
                 grind)
              | exact superpose b11e1096 b11e558
              | exact resolve b11e558 b11e1096
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e558 b11e1096
            have b11e2512 : (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y))) (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y)))) := by
              first
              | (have i₁ := b11e45 (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y)))
                 have i₂ := b11e680 (M.op (M.op (σ x) (σ x)) (σ y))
                 grind)
              | exact superpose b11e680 b11e45
              | exact resolve b11e45 b11e680
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e45 b11e680
            have b11e2523 : (σ y) = (M.op (M.op (M.op (σ (M.op x x)) (σ y)) (M.op (σ (M.op x x)) (σ y))) (M.op (M.op (σ (M.op x x)) (σ y)) (M.op (σ (M.op x x)) (σ y)))) := by
              first
              | (have i₁ := b11e2512
                 have i₂ := b11e67 x
                 grind)
              | exact superpose b11e67 b11e2512
              | exact resolve b11e2512 b11e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2512
            have b11e2531 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
              first
              | (have i₁ := b11e2523
                 have i₂ := b11e705
                 grind)
              | exact superpose b11e705 b11e2523
              | exact resolve b11e2523 b11e705
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2523
            have b11e2534 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
              first
              | (have i₁ := b11e2531
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e2531
              | exact resolve b11e2531 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2531
            have b11e2536 : (σ y) = (M.op (M.op (σ (M.op x x)) (σ (M.op x x))) (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
              first
              | (have i₁ := b11e2534
                 have i₂ := b11e67 x
                 grind)
              | exact superpose b11e67 b11e2534
              | exact resolve b11e2534 b11e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2534
            have b11e2537 : (σ y) = (M.op (σ (M.op (M.op x x) (M.op x x))) (σ (M.op (M.op x x) (M.op x x)))) := by
              first
              | (have i₁ := b11e2536
                 have i₂ := b11e67 (M.op x x)
                 grind)
              | exact superpose b11e67 b11e2536
              | exact resolve b11e2536 b11e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2536
            have b11e2538 : (σ y) = (σ (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) (M.op x x)))) := by
              first
              | (have i₁ := b11e2537
                 have i₂ := b11e67 (M.op (M.op x x) (M.op x x))
                 grind)
              | exact superpose b11e67 b11e2537
              | exact resolve b11e2537 b11e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e67 b11e2537
            have b11e2539 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) := by
              first
              | (have i₁ := b11e2538
                 have i₂ := b11e1340 x
                 grind)
              | exact superpose b11e1340 b11e2538
              | exact resolve b11e2538 b11e1340
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2538
            have b11e2540 : (σ y) = (σ (M.op x x)) := by
              first
              | (have i₁ := b11e2539
                 have i₂ := b11e1340 x
                 grind)
              | exact superpose b11e1340 b11e2539
              | exact resolve b11e2539 b11e1340
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1340 b11e2539
            have b11e2541 : (σ x) = (σ y) := by
              first
              | (have i₁ := b11e2540
                 have i₂ := b11e705
                 grind)
              | exact superpose b11e705 b11e2540
              | exact resolve b11e2540 b11e705
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e705 b11e2540
            have b11e2615 : y = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 y
                 have i₂ := b11e2541
                 grind)
              | exact superpose b11e2541 b11e15
              | exact resolve b11e15 b11e2541
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2541
            have b11e2632 : x = y := by
              first
              | (have i₁ := b11e2615
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e2615
              | exact resolve b11e2615 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2615
            have b11e2700 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b11e206
                 have i₂ := b11e2632
                 grind)
              | exact superpose b11e2632 b11e206
              | exact resolve b11e206 b11e2632
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e206 b11e2632
            have b11e2703 : False := by grind
            exact b11e2703
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b12e23 : (M.op x x) = (M.op y x) := by grind
            have b12e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
            have b12e26 : (M.op y x) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b12e14 X0 X2 X3
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e481 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e31 X0 X2 X0 X1
                 have i₂ := b12e14 X0 X0 X1
                 grind)
              | exact superpose b12e14 b12e31
              | exact resolve b12e31 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e31
            have b12e535 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X1 X1 x
                 have i₂ := b12e481 X1 x X0
                 grind)
              | exact superpose b12e481 b12e14
              | exact resolve b12e14 b12e481
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e481
            have b12e597 : y = (M.op y (M.op y (M.op y x))) := by
              first
              | (have i₁ := b12e535 y y
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e535
              | exact resolve b12e535 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e602 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
              intro X0
              first
              | (have i₁ := b12e535 X0 (M.op X0 X0)
                 have i₂ := b12e535 X0 X0
                 grind)
              | exact superpose b12e535 b12e535
              | exact resolve b12e535 b12e535
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e535
            have b12e617 : y = (M.op y (M.op y (M.op x x))) := by
              first
              | (have i₁ := b12e597
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e597
              | exact resolve b12e597 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e597
            have b12e718 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X0 X1 X0
                 have i₂ := b12e602 X0
                 grind)
              | exact superpose b12e602 b12e14
              | exact resolve b12e14 b12e602
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e602
            have b12e1067 : x = y := by
              first
              | (have i₁ := b12e617
                 have i₂ := b12e718 x y
                 grind)
              | exact superpose b12e718 b12e617
              | exact resolve b12e617 b12e718
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e617 b12e718
            have b12e1152 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b12e24
                 have i₂ := b12e1067
                 grind)
              | exact superpose b12e1067 b12e24
              | exact resolve b12e24 b12e1067
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1067
            have b12e1160 : False := by grind
            exact b12e1160
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b13e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b13e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b13e20 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e23 : (M.op x y) ≠ (M.op x x) := by grind
              have b13e24 : (M.op x x) = (M.op y x) := by grind
              have b13e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b13e15 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                   have i₂ := b13e15 X0 X2 X3
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e36 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e15 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
                   have i₂ := b13e15 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b13e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b13e21 X0 X0
                   have i₂ := b13e61 (σ X0)
                   grind)
                | exact superpose b13e61 b13e21
                | exact resolve b13e21 b13e61
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b13e65 X0
                   have i₂ := b13e61 X0
                   grind)
                | exact superpose b13e61 b13e65
                | exact resolve b13e65 b13e61
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e61 b13e65
              have b13e78 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (M.op y X0) ∨ y = (k y X0) := by
                intro X0
                first
                | (have i₁ := b13e19 y x
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e19
                | (have j0 := b13e19 y X0
                   grind)
                | (have r₁ := b13e19 y x
                   have r₂ := b13e28
                   grind)
                | exact resolve b13e19 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e90 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X1) = (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e20 X0 X1
                   have i₂ := b13e20 X0 X1
                   grind)
                | (have i₁ := b13e20 X0 X1
                   have i₂ := b13e20 X0 X0
                   grind)
                | exact superpose b13e20 b13e20
                | (have j0 := b13e20 X1 X0
                   have j1 := b13e20 X1 X0
                   grind)
                | exact resolve b13e20 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e101 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b13e18 X0 X1
                   have i₂ := b13e20 X0 X1
                   grind)
                | (have i₁ := b13e18 X0 X0
                   have i₂ := b13e20 X0 X1
                   grind)
                | exact superpose b13e20 b13e18
                | (have j0 := b13e18 X0 X0
                   have j1 := b13e20 X0 X1
                   grind)
                | (have r₁ := b13e18 X0 X1
                   have r₂ := b13e20 X0 X1
                   grind)
                | (have r₁ := b13e18 X1 X1
                   have r₂ := b13e20 X1 X1
                   grind)
                | (have r₁ := b13e18 X0 X0
                   have r₂ := b13e20 X0 X0
                   grind)
                | exact resolve b13e18 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e108 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e18 X1 X2
                   have i₂ := b13e20 X1 X0
                   grind)
                | (have i₁ := b13e18 X0 X1
                   have i₂ := b13e20 X0 X0
                   grind)
                | exact superpose b13e20 b13e18
                | (have j0 := b13e18 X1 X2
                   have j1 := b13e20 X1 X0
                   grind)
                | (have r₁ := b13e18 X0 X1
                   have r₂ := b13e20 X0 X1
                   grind)
                | (have r₁ := b13e18 X1 X1
                   have r₂ := b13e20 X1 X1
                   grind)
                | (have r₁ := b13e18 X0 X0
                   have r₂ := b13e20 X0 X0
                   grind)
                | exact resolve b13e18 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b13e19 X0 X1
                   have i₂ := b13e20 X0 X1
                   grind)
                | (have i₁ := b13e19 X0 X0
                   have i₂ := b13e20 X0 X1
                   grind)
                | exact superpose b13e20 b13e19
                | (have j0 := b13e19 X0 X1
                   have j1 := b13e20 X0 X1
                   grind)
                | (have r₁ := b13e19 X1 X1
                   have r₂ := b13e20 X1 X1
                   grind)
                | (have r₁ := b13e19 X0 X1
                   have r₂ := b13e20 X0 X1
                   grind)
                | (have r₁ := b13e19 X0 X0
                   have r₂ := b13e20 X0 X0
                   grind)
                | exact resolve b13e19 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e120 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b13e109 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e109
              have b13e121 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b13e120 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e120
              have b13e123 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b13e101 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e101
              have b13e124 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b13e123 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e123
              have b13e130 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b13e121 X0 X1
                   have j1 := b13e18 X0 X1
                   grind)
                | (have r₁ := b13e121 X0 X1
                   have r₂ := b13e18 X0 X1
                   grind)
                | (have r₁ := b13e121 X1 X1
                   have r₂ := b13e18 X1 X1
                   grind)
                | exact resolve b13e121 b13e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e121
              have b13e131 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have j0 := b13e108 X0 X1 X2
                   have j1 := b13e18 X1 X2
                   grind)
                | (have r₁ := b13e108 X1 X1 X2
                   have r₂ := b13e18 X1 X1
                   grind)
                | (have r₁ := b13e108 X1 X0 X2
                   have r₂ := b13e18 X0 X1
                   grind)
                | exact resolve b13e108 b13e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e108
              have b13e136 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X1) = (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have j0 := b13e90 X0 X1 X2
                   have j1 := b13e18 X1 X2
                   grind)
                | (have r₁ := b13e90 X1 X1 X1
                   have r₂ := b13e18 X1 X1
                   grind)
                | (have r₁ := b13e90 X0 X0 X0
                   have r₂ := b13e18 X0 X0
                   grind)
                | (have r₁ := b13e90 X0 X0 X1
                   have r₂ := b13e18 X0 X1
                   grind)
                | exact resolve b13e90 b13e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e90
              have b13e141 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have j0 := b13e136 X0 X1 X2
                   have j1 := b13e131 X2 X1 X2
                   grind)
                | (have r₁ := b13e136 X0 X2 X2
                   have r₂ := b13e131 X0 X2 X2
                   grind)
                | (have r₁ := b13e136 X1 X1 X0
                   have r₂ := b13e131 X0 X1 X1
                   grind)
                | (have r₁ := b13e136 X0 X1 X2
                   have r₂ := b13e131 X0 X1 X2
                   grind)
                | exact resolve b13e136 b13e131
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e131 b13e136
              have b13e169 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b13e130 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e130
              have b13e220 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b13e21 X1 X0
                   have i₂ := b13e124 (σ X1) (σ X0)
                   grind)
                | exact superpose b13e124 b13e21
                | (have j1 := b13e124 (σ X1) (σ X0)
                   grind)
                | exact resolve b13e21 b13e124
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e124
              have b13e244 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b13e220 X0 X1
                   have i₂ := b13e72 X1
                   grind)
                | exact superpose b13e72 b13e220
                | (have j0 := b13e220 X0 X1
                   grind)
                | exact resolve b13e220 b13e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e220
              have b13e393 : (M.op x y) = (M.op y x) ∨ y = (k y x) := by
                first
                | (have j0 := b13e78 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e78
              have b13e394 : (M.op x y) = (M.op x x) ∨ y = (k y x) := by
                first
                | (have i₁ := b13e393
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e393
                | exact resolve b13e393 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e393
              have b13e395 : y = (k y x) := by
                first
                | (have r₁ := b13e394
                   have r₂ := b13e23
                   grind)
                | exact resolve b13e394 b13e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e394
              have b13e424 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e35 X0 X2 X0 X1
                   have i₂ := b13e15 X0 X0 X1
                   grind)
                | exact superpose b13e15 b13e35
                | exact resolve b13e35 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e35
              have b13e463 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b13e424 X1 x X3
                   have i₂ := b13e424 X1 x X0
                   grind)
                | exact superpose b13e424 b13e424
                | exact resolve b13e424 b13e424
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e473 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X1 X1 x
                   have i₂ := b13e424 X1 x X0
                   grind)
                | exact superpose b13e424 b13e15
                | exact resolve b13e15 b13e424
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e424
              have b13e527 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
                intro X0
                first
                | (have i₁ := b13e473 X0 (M.op X0 X0)
                   have i₂ := b13e473 X0 X0
                   grind)
                | exact superpose b13e473 b13e473
                | exact resolve b13e473 b13e473
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e534 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e36 (M.op X0 (M.op X0 X1)) X1 X1
                   have i₂ := b13e473 X0 X1
                   grind)
                | exact superpose b13e473 b13e36
                | exact resolve b13e36 b13e473
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e539 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e534 X1 X0 X2
                   have i₂ := b13e473 X0 X1
                   grind)
                | exact superpose b13e473 b13e534
                | exact resolve b13e534 b13e473
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e534
              have b13e774 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b13e22
                   have i₂ := b13e141 (σ x) (σ y) X0
                   grind)
                | (have i₁ := b13e22
                   have i₂ := b13e141 X0 (σ y) (σ x)
                   grind)
                | exact superpose b13e141 b13e22
                | (have j1 := b13e141 (σ x) (σ y) (σ x)
                   grind)
                | exact resolve b13e22 b13e141
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e141
              have b13e799 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b13e774 X0
                   have i₂ := b13e21 y x
                   grind)
                | exact superpose b13e21 b13e774
                | (have j0 := b13e774 X0
                   grind)
                | exact resolve b13e774 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e774
              have b13e817 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b13e799 X0
                   have i₂ := b13e395
                   grind)
                | exact superpose b13e395 b13e799
                | (have j0 := b13e799 X0
                   grind)
                | exact resolve b13e799 b13e395
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e799
              have b13e837 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b13e36 X0 X1 X0
                   have i₂ := b13e527 X0
                   grind)
                | exact superpose b13e527 b13e36
                | exact resolve b13e36 b13e527
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e36
              have b13e838 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X0 X1 X0
                   have i₂ := b13e527 X0
                   grind)
                | exact superpose b13e527 b13e15
                | exact resolve b13e15 b13e527
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e527
              have b13e1370 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e463 X1 (M.op X2 (M.op X0 X0)) X2
                   have i₂ := b13e838 X0 X2
                   grind)
                | exact superpose b13e838 b13e463
                | exact resolve b13e463 b13e838
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e2875 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e539 (M.op X1 (M.op X0 X0)) X2 X1
                   have i₂ := b13e838 X0 X1
                   grind)
                | exact superpose b13e838 b13e539
                | exact resolve b13e539 b13e838
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e539
              have b13e3056 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b13e2875 X0 X1 x
                   have i₂ := b13e1370 X0 x X1
                   grind)
                | exact superpose b13e1370 b13e2875
                | exact resolve b13e2875 b13e1370
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1370 b13e2875
              have b13e4622 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b13e837 X1 X1
                   have i₂ := b13e463 X1 X1 X0
                   grind)
                | (have i₁ := b13e837 X1 X1
                   have i₂ := b13e463 X0 X1 X1
                   grind)
                | exact superpose b13e463 b13e837
                | exact resolve b13e837 b13e463
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e463 b13e837
              have b13e5361 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e244 x y
                   grind)
                | exact superpose b13e244 b13e22
                | (have j1 := b13e244 x y
                   grind)
                | exact resolve b13e22 b13e244
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e244
              have b13e5433 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b13e5361
                   have i₂ := b13e395
                   grind)
                | exact superpose b13e395 b13e5361
                | exact resolve b13e5361 b13e395
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e395 b13e5361
              have b13e5483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have i₁ := b13e5433
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e5433
                | exact resolve b13e5433 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e5433
              have b13e5517 : (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have r₁ := b13e5483
                   have r₂ := b13e22
                   grind)
                | exact resolve b13e5483 b13e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e5483
              have b13e8276 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b13e838 X0 X1
                   have i₂ := b13e3056 X0 X1
                   grind)
                | (have i₁ := b13e838 X0 X0
                   have i₂ := b13e3056 X0 X0
                   grind)
                | exact superpose b13e3056 b13e838
                | exact resolve b13e838 b13e3056
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e838
              have b13e9174 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b13e19 X0 (M.op X1 (M.op X1 X0))
                   have i₂ := b13e4622 X1 X0
                   grind)
                | exact superpose b13e4622 b13e19
                | (have j0 := b13e19 X0 (M.op X1 (M.op X1 X0))
                   grind)
                | (have r₁ := b13e19 X1 (M.op X0 (M.op X0 X1))
                   have r₂ := b13e4622 X0 X1
                   grind)
                | exact resolve b13e19 b13e4622
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e9190 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b13e169 X0 (M.op X1 (M.op X1 X0))
                   have i₂ := b13e4622 X1 X0
                   grind)
                | exact superpose b13e4622 b13e169
                | (have j0 := b13e169 X0 X0
                   grind)
                | exact resolve b13e169 b13e4622
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e169
              have b13e9221 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have i₁ := b13e817 (M.op X0 (M.op X0 (σ y)))
                   have i₂ := b13e4622 X0 (σ y)
                   grind)
                | exact superpose b13e4622 b13e817
                | (have j0 := b13e817 (σ y)
                   grind)
                | exact resolve b13e817 b13e4622
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e817 b13e4622
              have b13e9235 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have j0 := b13e9174 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9174
              have b13e9245 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have i₁ := b13e9221 X0
                   have i₂ := b13e72 y
                   grind)
                | exact superpose b13e72 b13e9221
                | (have j0 := b13e9221 X0
                   grind)
                | exact resolve b13e9221 b13e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9221
              have b13e9263 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b13e9235 X0 X1
                   have i₂ := b13e473 X1 X0
                   grind)
                | exact superpose b13e473 b13e9235
                | (have j0 := b13e9235 X0 X1
                   grind)
                | exact resolve b13e9235 b13e473
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e473 b13e9235
              have b13e9316 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have i₁ := b13e9245 X0
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e9245
                | (have j0 := b13e9245 X0
                   grind)
                | exact resolve b13e9245 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9245
              have b13e9317 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have j0 := b13e9316 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9316
              have b13e9332 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have j0 := b13e9263 X0 X1
                   have j1 := b13e9190 X0 X1
                   grind)
                | (have r₁ := b13e9263 X0 X1
                   have r₂ := b13e9190 X0 X1
                   grind)
                | exact resolve b13e9263 b13e9190
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9190 b13e9263
              have b13e9357 : ∀ X0 : G, (σ (M.op y y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b13e9317 X0
                   have i₂ := b13e72 y
                   grind)
                | exact superpose b13e72 b13e9317
                | exact resolve b13e9317 b13e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9317
              have b13e9371 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e9357 x
                   have i₂ := b13e9332 (σ y) x
                   grind)
                | exact superpose b13e9332 b13e9357
                | exact resolve b13e9357 b13e9332
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9332 b13e9357
              have b13e9377 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e9371
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e9371
                | exact resolve b13e9371 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9371
              have b13e9380 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b13e9377
                   have r₂ := b13e5517
                   grind)
                | exact resolve b13e9377 b13e5517
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9377
              have b13e9531 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) := by
                first
                | (have i₁ := b13e3056 (σ y) (σ x)
                   have i₂ := b13e9380
                   grind)
                | exact superpose b13e9380 b13e3056
                | exact resolve b13e3056 b13e9380
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e3056
              have b13e9533 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) := by
                first
                | (have i₁ := b13e8276 (σ y) (σ x)
                   have i₂ := b13e9380
                   grind)
                | exact superpose b13e9380 b13e8276
                | exact resolve b13e8276 b13e9380
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e8276 b13e9380
              have b13e9537 : (σ y) = (M.op (σ x) (σ (M.op y y))) := by
                first
                | (have i₁ := b13e9533
                   have i₂ := b13e72 y
                   grind)
                | exact superpose b13e72 b13e9533
                | exact resolve b13e9533 b13e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9533
              have b13e9538 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op y y))) := by
                first
                | (have i₁ := b13e9531
                   have i₂ := b13e72 y
                   grind)
                | exact superpose b13e72 b13e9531
                | exact resolve b13e9531 b13e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e72 b13e9531
              have b13e9554 : (σ y) = (M.op (σ x) (σ (M.op x y))) := by
                first
                | (have i₁ := b13e9537
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e9537
                | exact resolve b13e9537 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9537
              have b13e9555 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
                first
                | (have i₁ := b13e9538
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e9538
                | exact resolve b13e9538 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9538
              have b13e9563 : (σ (M.op x y)) = (σ y) := by
                first
                | (have i₁ := b13e9555
                   have i₂ := b13e9554
                   grind)
                | exact superpose b13e9554 b13e9555
                | exact resolve b13e9555 b13e9554
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e9554 b13e9555
              have b13e9567 : False := by grind
              exact b13e9567
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e28 : (M.op x y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X1 (τ X0)
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e21
                | exact resolve b14e21 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                   have i₂ := b14e15 X0 X2 X3
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e37 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
                   have i₂ := b14e15 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b14e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e73 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
                intro X0
                first
                | (have i₁ := b14e30 X0 (τ X0)
                   have i₂ := b14e68 (τ X0)
                   grind)
                | exact superpose b14e68 b14e30
                | exact resolve b14e30 b14e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e30
              have b14e76 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b14e73 X0
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e73
                | exact resolve b14e73 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e73
              have b14e82 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b14e76 X0
                   have i₂ := b14e68 X0
                   grind)
                | exact superpose b14e68 b14e76
                | exact resolve b14e76 b14e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e68 b14e76
              have b14e109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e18 X0 X1
                   have i₂ := b14e20 X0 X1
                   grind)
                | (have i₁ := b14e18 X0 X0
                   have i₂ := b14e20 X0 X1
                   grind)
                | exact superpose b14e20 b14e18
                | (have j0 := b14e18 X0 X0
                   have j1 := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e18 X0 X1
                   have r₂ := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e18 X1 X1
                   have r₂ := b14e20 X1 X1
                   grind)
                | (have r₁ := b14e18 X0 X0
                   have r₂ := b14e20 X0 X0
                   grind)
                | exact resolve b14e18 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e117 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e19 X0 X1
                   have i₂ := b14e20 X0 X1
                   grind)
                | (have i₁ := b14e19 X0 X0
                   have i₂ := b14e20 X0 X1
                   grind)
                | exact superpose b14e20 b14e19
                | (have j0 := b14e19 X0 X1
                   have j1 := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e19 X1 X1
                   have r₂ := b14e20 X1 X1
                   grind)
                | (have r₁ := b14e19 X0 X1
                   have r₂ := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e19 X0 X0
                   have r₂ := b14e20 X0 X0
                   grind)
                | exact resolve b14e19 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e129 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b14e117 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e117
              have b14e130 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b14e129 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e129
              have b14e132 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b14e109 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e109
              have b14e133 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b14e132 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e132
              have b14e140 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b14e130 X0 X1
                   have j1 := b14e18 X0 X1
                   grind)
                | (have r₁ := b14e130 X0 X1
                   have r₂ := b14e18 X0 X1
                   grind)
                | (have r₁ := b14e130 X1 X1
                   have r₂ := b14e18 X1 X1
                   grind)
                | exact resolve b14e130 b14e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e130
              have b14e170 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e140 (σ X0) (σ X1)
                   have i₂ := b14e21 X0 X1
                   grind)
                | exact superpose b14e21 b14e140
                | exact resolve b14e140 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e140
              have b14e189 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b14e16 (M.op (τ X0) (τ X0))
                   have i₂ := b14e82 X0
                   grind)
                | exact superpose b14e82 b14e16
                | exact resolve b14e16 b14e82
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e82
              have b14e322 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e37 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
                   have i₂ := b14e15 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
                   grind)
                | exact superpose b14e15 b14e37
                | exact resolve b14e37 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e335 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) = X2 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X2 (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) X1
                   have i₂ := b14e37 (M.op (M.op X1 X2) X2) X3 X0
                   grind)
                | exact superpose b14e37 b14e15
                | exact resolve b14e15 b14e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e387 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e36 X0 X2 X0 X1
                   have i₂ := b14e15 X0 X0 X1
                   grind)
                | exact superpose b14e15 b14e36
                | exact resolve b14e36 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e36
              have b14e424 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b14e387 X1 x X3
                   have i₂ := b14e387 X1 x X0
                   grind)
                | exact superpose b14e387 b14e387
                | exact resolve b14e387 b14e387
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e434 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X1 X1 x
                   have i₂ := b14e387 X1 x X0
                   grind)
                | exact superpose b14e387 b14e15
                | exact resolve b14e15 b14e387
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e441 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e37 X0 (M.op X2 X0) X2
                   have i₂ := b14e387 X0 X1 (M.op X2 X0)
                   grind)
                | exact superpose b14e387 b14e37
                | exact resolve b14e37 b14e387
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e387
              have b14e452 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e441 X0 X1 X2
                   have i₂ := b14e37 X0 X0 X1
                   grind)
                | exact superpose b14e37 b14e441
                | exact resolve b14e441 b14e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e441
              have b14e486 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
                intro X0
                first
                | (have i₁ := b14e434 X0 (M.op X0 X0)
                   have i₂ := b14e434 X0 X0
                   grind)
                | exact superpose b14e434 b14e434
                | exact resolve b14e434 b14e434
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e493 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e37 (M.op X0 (M.op X0 X1)) X1 X1
                   have i₂ := b14e434 X0 X1
                   grind)
                | exact superpose b14e434 b14e37
                | exact resolve b14e37 b14e434
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e497 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e493 X1 X0 X2
                   have i₂ := b14e434 X0 X1
                   grind)
                | exact superpose b14e434 b14e493
                | exact resolve b14e493 b14e434
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e493
              have b14e583 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e37 X0 X1 X0
                   have i₂ := b14e486 X0
                   grind)
                | exact superpose b14e486 b14e37
                | exact resolve b14e37 b14e486
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e584 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 X1 X0
                   have i₂ := b14e486 X0
                   grind)
                | exact superpose b14e486 b14e15
                | exact resolve b14e15 b14e486
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e597 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e434 (M.op X0 X0) X0
                   have i₂ := b14e486 X0
                   grind)
                | exact superpose b14e486 b14e434
                | exact resolve b14e434 b14e486
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e875 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e424 X1 (M.op X2 (M.op X0 X0)) X2
                   have i₂ := b14e584 X0 X2
                   grind)
                | exact superpose b14e584 b14e424
                | exact resolve b14e424 b14e584
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e876 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e424 X1 (M.op X2 (M.op X2 X0)) X0
                   have i₂ := b14e434 X2 X0
                   grind)
                | exact superpose b14e434 b14e424
                | exact resolve b14e424 b14e434
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e1067 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e452 (M.op X2 (M.op X2 X0)) X0 X1
                   have i₂ := b14e434 X2 X0
                   grind)
                | exact superpose b14e434 b14e452
                | exact resolve b14e452 b14e434
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e1127 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e486 X1
                   have i₂ := b14e452 X1 X0 X1
                   grind)
                | (have i₁ := b14e486 X1
                   have i₂ := b14e452 X1 X1 X0
                   grind)
                | exact superpose b14e452 b14e486
                | exact resolve b14e486 b14e452
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e452 b14e486
              have b14e1167 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) := by
                intro X0 X2
                first
                | (have i₁ := b14e1067 X0 x X2
                   have i₂ := b14e1127 x (M.op X2 (M.op X2 X0))
                   grind)
                | exact superpose b14e1127 b14e1067
                | exact resolve b14e1067 b14e1127
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1067
              have b14e1193 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
                intro X0 X2
                first
                | (have i₁ := b14e1167 X0 X2
                   have i₂ := b14e434 X2 X0
                   grind)
                | exact superpose b14e434 b14e1167
                | exact resolve b14e1167 b14e434
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e434 b14e1167
              have b14e1716 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e497 (M.op X1 (M.op X0 X0)) X2 X1
                   have i₂ := b14e584 X0 X1
                   grind)
                | exact superpose b14e584 b14e497
                | exact resolve b14e497 b14e584
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e584
              have b14e1851 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e1716 X0 X1 x
                   have i₂ := b14e875 X0 x X1
                   grind)
                | exact superpose b14e875 b14e1716
                | exact resolve b14e1716 b14e875
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e875 b14e1716
              have b14e3371 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
                intro X0
                first
                | (have i₁ := b14e597 (τ X0)
                   have i₂ := b14e189 X0
                   grind)
                | exact superpose b14e189 b14e597
                | exact resolve b14e597 b14e189
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e597
              have b14e3422 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
                intro X0
                first
                | (have i₁ := b14e3371 X0
                   have i₂ := b14e189 (M.op X0 X0)
                   grind)
                | exact superpose b14e189 b14e3371
                | exact resolve b14e3371 b14e189
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e189 b14e3371
              have b14e3436 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
                intro X0
                first
                | (have i₁ := b14e3422 X0
                   have i₂ := b14e1851 X0 (M.op X0 X0)
                   grind)
                | exact superpose b14e1851 b14e3422
                | exact resolve b14e3422 b14e1851
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e3422
              have b14e3449 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
                intro X0
                first
                | (have i₁ := b14e3436 X0
                   have i₂ := b14e1127 X0 X0
                   grind)
                | exact superpose b14e1127 b14e3436
                | exact resolve b14e3436 b14e1127
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e3436
              have b14e4457 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e583 X0 X1
                   have i₂ := b14e1851 X0 X1
                   grind)
                | (have i₁ := b14e583 X0 X0
                   have i₂ := b14e1851 X0 X0
                   grind)
                | exact superpose b14e1851 b14e583
                | exact resolve b14e583 b14e1851
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e583
              have b14e4565 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e497 X1 X0 X0
                   have i₂ := b14e1851 (M.op X0 X1) X0
                   grind)
                | exact superpose b14e1851 b14e497
                | exact resolve b14e497 b14e1851
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e497
              have b14e4817 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e170 y x
                   grind)
                | exact superpose b14e170 b14e22
                | (have j1 := b14e170 y x
                   grind)
                | exact resolve b14e22 b14e170
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e170
              have b14e11466 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ (M.op X0 (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b14e3449 X1
                   have i₂ := b14e424 X1 X1 X0
                   grind)
                | (have i₁ := b14e3449 X1
                   have i₂ := b14e424 X0 X1 X1
                   grind)
                | exact superpose b14e424 b14e3449
                | exact resolve b14e3449 b14e424
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e424 b14e3449
              have b14e12557 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e11466 X0 (σ X0)
                   have i₂ := b14e16 X0
                   grind)
                | exact superpose b14e16 b14e11466
                | exact resolve b14e11466 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e11466
              have b14e13483 : ∀ X0 X1 X2 : G, (M.op X0 (τ (M.op X1 (M.op X1 (σ X0))))) = (M.op (M.op X2 (M.op X0 (τ (M.op X1 (M.op X1 (σ X0)))))) (τ (M.op X1 (M.op X1 (σ X0))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e37 (τ (M.op X1 (M.op X1 (σ X0)))) X1 X0
                   have i₂ := b14e12557 X0 X1
                   grind)
                | exact superpose b14e12557 b14e37
                | exact resolve b14e37 b14e12557
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e37
              have b14e13516 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op X1 (M.op X1 (σ X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b14e4565 X0 (τ (M.op X1 (M.op X1 (σ X0))))
                   have i₂ := b14e12557 X0 X1
                   grind)
                | exact superpose b14e12557 b14e4565
                | exact resolve b14e4565 b14e12557
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e4565
              have b14e13544 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e13483 X0 X1 X2
                   have i₂ := b14e12557 X0 X1
                   grind)
                | exact superpose b14e12557 b14e13483
                | exact resolve b14e13483 b14e12557
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e13483
              have b14e20957 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) X0)) (M.op (M.op X3 X0) X0))) X0) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 (M.op (M.op X3 X0) X0) (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) X0)) (M.op (M.op X3 X0) X0))) X2
                   have i₂ := b14e335 X2 X3 X0 X1
                   grind)
                | exact superpose b14e335 b14e15
                | exact resolve b14e15 b14e335
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e335
              have b14e21051 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X0) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X3 X0) X0))) X0) := by
                intro X0 X1 X3
                first
                | (have i₁ := b14e20957 X0 X1 x X3
                   have i₂ := b14e322 X0 x X3
                   grind)
                | exact superpose b14e322 b14e20957
                | exact resolve b14e20957 b14e322
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e322 b14e20957
              have b14e21208 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e21051 X1 X1 X0
                   have i₂ := b14e1127 X0 X1
                   grind)
                | exact superpose b14e1127 b14e21051
                | exact resolve b14e21051 b14e1127
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1127 b14e21051
              have b14e26034 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X1 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e21208 (M.op X1 (M.op X1 X0)) X2
                   have i₂ := b14e876 X0 (M.op X1 (M.op X1 X0)) X1
                   grind)
                | exact superpose b14e876 b14e21208
                | exact resolve b14e21208 b14e876
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e876 b14e21208
              have b14e26155 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e26034 X0 X1 X2
                   have i₂ := b14e1193 X0 X1
                   grind)
                | exact superpose b14e1193 b14e26034
                | exact resolve b14e26034 b14e1193
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1193 b14e26034
              have b14e41002 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e26155 X0 X2 X1
                   have i₂ := b14e1851 X0 X1
                   grind)
                | (have i₁ := b14e26155 X0 X1 X0
                   have i₂ := b14e1851 X0 X0
                   grind)
                | exact superpose b14e1851 b14e26155
                | exact resolve b14e26155 b14e1851
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1851 b14e26155
              have b14e106188 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op X0 (M.op X0 (σ (σ X1))))))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e12557 X1 (σ X1)
                   have i₂ := b14e13516 (σ X1) X0
                   grind)
                | exact superpose b14e13516 b14e12557
                | exact resolve b14e12557 b14e13516
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e12557
              have b14e109062 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (τ (τ (M.op X0 (M.op X0 (σ (σ X1))))))) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e13544 X1 (σ X1) X2
                   have i₂ := b14e13516 (σ X1) X0
                   grind)
                | exact superpose b14e13516 b14e13544
                | exact resolve b14e13544 b14e13516
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e13516 b14e13544
              have b14e148774 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b14e4817
                   have i₂ := b14e133 y x
                   grind)
                | exact superpose b14e133 b14e4817
                | (have j1 := b14e133 y x
                   grind)
                | exact resolve b14e4817 b14e133
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e133 b14e4817
              have b14e148779 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
              clear b14e148774
              have b14e148780 : (σ (M.op x y)) = (σ y) := by
                first
                | (have r₁ := b14e148779
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e148779 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e148779
              have b14e148825 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (τ (τ (M.op X0 (M.op X0 (σ (σ y))))))) := by
                intro X0
                first
                | (have i₁ := b14e106188 X0 (M.op x y)
                   have i₂ := b14e148780
                   grind)
                | exact superpose b14e148780 b14e106188
                | exact resolve b14e106188 b14e148780
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e106188 b14e148780
              have b14e148826 : y = (M.op x y) := by
                first
                | (have i₁ := b14e148825 x
                   have i₂ := b14e109062 x y x
                   grind)
                | exact superpose b14e109062 b14e148825
                | exact resolve b14e148825 b14e109062
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e109062 b14e148825
              have b14e148948 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 y)) (M.op x y)) := by
                intro X0
                first
                | (have i₁ := b14e41002 y X0 x
                   have i₂ := b14e148826
                   grind)
                | exact superpose b14e148826 b14e41002
                | exact resolve b14e41002 b14e148826
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e41002
              have b14e148973 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 y)) y) := by
                intro X0
                first
                | (have i₁ := b14e148948 X0
                   have i₂ := b14e148826
                   grind)
                | exact superpose b14e148826 b14e148948
                | exact resolve b14e148948 b14e148826
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e148948
              have b14e148998 : y = (M.op y y) := by
                first
                | (have i₁ := b14e148973 x
                   have i₂ := b14e4457 y x
                   grind)
                | exact superpose b14e4457 b14e148973
                | exact resolve b14e148973 b14e4457
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e4457 b14e148973
              have b14e149656 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b14e28
                   have i₂ := b14e148998
                   grind)
                | exact superpose b14e148998 b14e28
                | exact resolve b14e28 b14e148998
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e148998
              have b14e149879 : False := by grind
              exact b14e149879
        · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b15e23 : (M.op x x) = (M.op y x) := by grind
            have b15e25 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e26 : (M.op y x) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b15e14 X0 X2 X3
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e469 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e31 X0 X2 X0 X1
                 have i₂ := b15e14 X0 X0 X1
                 grind)
              | exact superpose b15e14 b15e31
              | exact resolve b15e31 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e31
            have b15e522 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 X1 x
                 have i₂ := b15e469 X1 x X0
                 grind)
              | exact superpose b15e469 b15e14
              | exact resolve b15e14 b15e469
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e469
            have b15e582 : y = (M.op y (M.op y (M.op y x))) := by
              first
              | (have i₁ := b15e522 y y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e522
              | exact resolve b15e522 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e587 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
              intro X0
              first
              | (have i₁ := b15e522 X0 (M.op X0 X0)
                 have i₂ := b15e522 X0 X0
                 grind)
              | exact superpose b15e522 b15e522
              | exact resolve b15e522 b15e522
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e522
            have b15e602 : y = (M.op y (M.op y (M.op x x))) := by
              first
              | (have i₁ := b15e582
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e582
              | exact resolve b15e582 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e582
            have b15e696 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X0 X1 X0
                 have i₂ := b15e587 X0
                 grind)
              | exact superpose b15e587 b15e14
              | exact resolve b15e14 b15e587
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e587
            have b15e1055 : x = y := by
              first
              | (have i₁ := b15e602
                 have i₂ := b15e696 x y
                 grind)
              | exact superpose b15e696 b15e602
              | exact resolve b15e602 b15e696
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e602 b15e696
            have b15e1141 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e1055
                 grind)
              | exact superpose b15e1055 b15e25
              | exact resolve b15e25 b15e1055
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1055
            have b15e1149 : False := by grind
            exact b15e1149
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b16e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b16e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b16e23 : (M.op x y) ≠ (M.op x x) := by grind
              have b16e24 : (M.op x x) = (M.op y x) := by grind
              have b16e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b16e15 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                   have i₂ := b16e15 X0 X2 X3
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e36 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e15 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
                   have i₂ := b16e15 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b16e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b16e21 X0 X0
                   have i₂ := b16e60 (σ X0)
                   grind)
                | exact superpose b16e60 b16e21
                | exact resolve b16e21 b16e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b16e64 X0
                   have i₂ := b16e60 X0
                   grind)
                | exact superpose b16e60 b16e64
                | exact resolve b16e64 b16e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e60 b16e64
              have b16e77 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (M.op y X0) ∨ y = (k y X0) := by
                intro X0
                first
                | (have i₁ := b16e19 y x
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e19
                | (have j0 := b16e19 y X0
                   grind)
                | (have r₁ := b16e19 y x
                   have r₂ := b16e28
                   grind)
                | exact resolve b16e19 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e85 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X1) = (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e20 X0 X1
                   have i₂ := b16e20 X0 X1
                   grind)
                | (have i₁ := b16e20 X0 X1
                   have i₂ := b16e20 X0 X0
                   grind)
                | exact superpose b16e20 b16e20
                | (have j0 := b16e20 X1 X0
                   have j1 := b16e20 X1 X0
                   grind)
                | exact resolve b16e20 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e96 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b16e18 X0 X1
                   have i₂ := b16e20 X0 X1
                   grind)
                | (have i₁ := b16e18 X0 X0
                   have i₂ := b16e20 X0 X1
                   grind)
                | exact superpose b16e20 b16e18
                | (have j0 := b16e18 X0 X0
                   have j1 := b16e20 X0 X1
                   grind)
                | (have r₁ := b16e18 X0 X1
                   have r₂ := b16e20 X0 X1
                   grind)
                | (have r₁ := b16e18 X1 X1
                   have r₂ := b16e20 X1 X1
                   grind)
                | (have r₁ := b16e18 X0 X0
                   have r₂ := b16e20 X0 X0
                   grind)
                | exact resolve b16e18 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e103 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e18 X1 X2
                   have i₂ := b16e20 X1 X0
                   grind)
                | (have i₁ := b16e18 X0 X1
                   have i₂ := b16e20 X0 X0
                   grind)
                | exact superpose b16e20 b16e18
                | (have j0 := b16e18 X1 X2
                   have j1 := b16e20 X1 X0
                   grind)
                | (have r₁ := b16e18 X0 X1
                   have r₂ := b16e20 X0 X1
                   grind)
                | (have r₁ := b16e18 X1 X1
                   have r₂ := b16e20 X1 X1
                   grind)
                | (have r₁ := b16e18 X0 X0
                   have r₂ := b16e20 X0 X0
                   grind)
                | exact resolve b16e18 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b16e19 X0 X1
                   have i₂ := b16e20 X0 X1
                   grind)
                | (have i₁ := b16e19 X0 X0
                   have i₂ := b16e20 X0 X1
                   grind)
                | exact superpose b16e20 b16e19
                | (have j0 := b16e19 X0 X1
                   have j1 := b16e20 X0 X1
                   grind)
                | (have r₁ := b16e19 X1 X1
                   have r₂ := b16e20 X1 X1
                   grind)
                | (have r₁ := b16e19 X0 X1
                   have r₂ := b16e20 X0 X1
                   grind)
                | (have r₁ := b16e19 X0 X0
                   have r₂ := b16e20 X0 X0
                   grind)
                | exact resolve b16e19 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b16e104 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e104
              have b16e116 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b16e115 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e115
              have b16e118 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b16e96 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e96
              have b16e119 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b16e118 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e118
              have b16e125 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b16e116 X0 X1
                   have j1 := b16e18 X0 X1
                   grind)
                | (have r₁ := b16e116 X0 X1
                   have r₂ := b16e18 X0 X1
                   grind)
                | (have r₁ := b16e116 X1 X1
                   have r₂ := b16e18 X1 X1
                   grind)
                | exact resolve b16e116 b16e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e116
              have b16e126 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have j0 := b16e103 X0 X1 X2
                   have j1 := b16e18 X1 X2
                   grind)
                | (have r₁ := b16e103 X1 X1 X2
                   have r₂ := b16e18 X1 X1
                   grind)
                | (have r₁ := b16e103 X1 X0 X2
                   have r₂ := b16e18 X0 X1
                   grind)
                | exact resolve b16e103 b16e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e103
              have b16e131 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X1) = (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have j0 := b16e85 X0 X1 X2
                   have j1 := b16e18 X1 X2
                   grind)
                | (have r₁ := b16e85 X1 X1 X1
                   have r₂ := b16e18 X1 X1
                   grind)
                | (have r₁ := b16e85 X0 X0 X0
                   have r₂ := b16e18 X0 X0
                   grind)
                | (have r₁ := b16e85 X0 X0 X1
                   have r₂ := b16e18 X0 X1
                   grind)
                | exact resolve b16e85 b16e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e85
              have b16e136 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have j0 := b16e131 X0 X1 X2
                   have j1 := b16e126 X2 X1 X2
                   grind)
                | (have r₁ := b16e131 X0 X2 X2
                   have r₂ := b16e126 X0 X2 X2
                   grind)
                | (have r₁ := b16e131 X1 X1 X0
                   have r₂ := b16e126 X0 X1 X1
                   grind)
                | (have r₁ := b16e131 X0 X1 X2
                   have r₂ := b16e126 X0 X1 X2
                   grind)
                | exact resolve b16e131 b16e126
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e126 b16e131
              have b16e164 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b16e125 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e125
              have b16e215 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b16e21 X1 X0
                   have i₂ := b16e119 (σ X1) (σ X0)
                   grind)
                | exact superpose b16e119 b16e21
                | (have j1 := b16e119 (σ X1) (σ X0)
                   grind)
                | exact resolve b16e21 b16e119
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e119
              have b16e239 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b16e215 X0 X1
                   have i₂ := b16e71 X1
                   grind)
                | exact superpose b16e71 b16e215
                | (have j0 := b16e215 X0 X1
                   grind)
                | exact resolve b16e215 b16e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e215
              have b16e382 : (M.op x y) = (M.op y x) ∨ y = (k y x) := by
                first
                | (have j0 := b16e77 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e77
              have b16e383 : (M.op x y) = (M.op x x) ∨ y = (k y x) := by
                first
                | (have i₁ := b16e382
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e382
                | exact resolve b16e382 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e382
              have b16e384 : y = (k y x) := by
                first
                | (have r₁ := b16e383
                   have r₂ := b16e23
                   grind)
                | exact resolve b16e383 b16e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e383
              have b16e412 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e35 X0 X2 X0 X1
                   have i₂ := b16e15 X0 X0 X1
                   grind)
                | exact superpose b16e15 b16e35
                | exact resolve b16e35 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e35
              have b16e450 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b16e412 X1 x X3
                   have i₂ := b16e412 X1 x X0
                   grind)
                | exact superpose b16e412 b16e412
                | exact resolve b16e412 b16e412
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e460 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X1 X1 x
                   have i₂ := b16e412 X1 x X0
                   grind)
                | exact superpose b16e412 b16e15
                | exact resolve b16e15 b16e412
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e412
              have b16e512 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
                intro X0
                first
                | (have i₁ := b16e460 X0 (M.op X0 X0)
                   have i₂ := b16e460 X0 X0
                   grind)
                | exact superpose b16e460 b16e460
                | exact resolve b16e460 b16e460
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e519 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e36 (M.op X0 (M.op X0 X1)) X1 X1
                   have i₂ := b16e460 X0 X1
                   grind)
                | exact superpose b16e460 b16e36
                | exact resolve b16e36 b16e460
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e524 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e519 X1 X0 X2
                   have i₂ := b16e460 X0 X1
                   grind)
                | exact superpose b16e460 b16e519
                | exact resolve b16e519 b16e460
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e519
              have b16e751 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b16e22
                   have i₂ := b16e136 (σ x) (σ y) X0
                   grind)
                | (have i₁ := b16e22
                   have i₂ := b16e136 X0 (σ y) (σ x)
                   grind)
                | exact superpose b16e136 b16e22
                | (have j1 := b16e136 (σ x) (σ y) (σ x)
                   grind)
                | exact resolve b16e22 b16e136
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e136
              have b16e777 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b16e751 X0
                   have i₂ := b16e21 y x
                   grind)
                | exact superpose b16e21 b16e751
                | (have j0 := b16e751 X0
                   grind)
                | exact resolve b16e751 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e751
              have b16e797 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b16e777 X0
                   have i₂ := b16e384
                   grind)
                | exact superpose b16e384 b16e777
                | (have j0 := b16e777 X0
                   grind)
                | exact resolve b16e777 b16e384
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e777
              have b16e820 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b16e36 X0 X1 X0
                   have i₂ := b16e512 X0
                   grind)
                | exact superpose b16e512 b16e36
                | exact resolve b16e36 b16e512
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e36
              have b16e821 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X0 X1 X0
                   have i₂ := b16e512 X0
                   grind)
                | exact superpose b16e512 b16e15
                | exact resolve b16e15 b16e512
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e512
              have b16e1347 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e450 X1 (M.op X2 (M.op X0 X0)) X2
                   have i₂ := b16e821 X0 X2
                   grind)
                | exact superpose b16e821 b16e450
                | exact resolve b16e450 b16e821
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e2839 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e524 (M.op X1 (M.op X0 X0)) X2 X1
                   have i₂ := b16e821 X0 X1
                   grind)
                | exact superpose b16e821 b16e524
                | exact resolve b16e524 b16e821
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e524
              have b16e3017 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b16e2839 X0 X1 x
                   have i₂ := b16e1347 X0 x X1
                   grind)
                | exact superpose b16e1347 b16e2839
                | exact resolve b16e2839 b16e1347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e1347 b16e2839
              have b16e4404 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b16e820 X1 X1
                   have i₂ := b16e450 X1 X1 X0
                   grind)
                | (have i₁ := b16e820 X1 X1
                   have i₂ := b16e450 X0 X1 X1
                   grind)
                | exact superpose b16e450 b16e820
                | exact resolve b16e820 b16e450
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e450 b16e820
              have b16e5497 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b16e22
                   have i₂ := b16e239 x y
                   grind)
                | exact superpose b16e239 b16e22
                | (have j1 := b16e239 x y
                   grind)
                | exact resolve b16e22 b16e239
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e239
              have b16e5570 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b16e5497
                   have i₂ := b16e384
                   grind)
                | exact superpose b16e384 b16e5497
                | exact resolve b16e5497 b16e384
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e384 b16e5497
              have b16e5622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have i₁ := b16e5570
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e5570
                | exact resolve b16e5570 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e5570
              have b16e5655 : (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have r₁ := b16e5622
                   have r₂ := b16e22
                   grind)
                | exact resolve b16e5622 b16e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e5622
              have b16e7791 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b16e821 X0 X1
                   have i₂ := b16e3017 X0 X1
                   grind)
                | (have i₁ := b16e821 X0 X0
                   have i₂ := b16e3017 X0 X0
                   grind)
                | exact superpose b16e3017 b16e821
                | exact resolve b16e821 b16e3017
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e821
              have b16e9169 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b16e19 X0 (M.op X1 (M.op X1 X0))
                   have i₂ := b16e4404 X1 X0
                   grind)
                | exact superpose b16e4404 b16e19
                | (have j0 := b16e19 X0 (M.op X1 (M.op X1 X0))
                   grind)
                | (have r₁ := b16e19 X1 (M.op X0 (M.op X0 X1))
                   have r₂ := b16e4404 X0 X1
                   grind)
                | exact resolve b16e19 b16e4404
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e9185 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b16e164 X0 (M.op X1 (M.op X1 X0))
                   have i₂ := b16e4404 X1 X0
                   grind)
                | exact superpose b16e4404 b16e164
                | (have j0 := b16e164 X0 X0
                   grind)
                | exact resolve b16e164 b16e4404
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e164
              have b16e9216 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have i₁ := b16e797 (M.op X0 (M.op X0 (σ y)))
                   have i₂ := b16e4404 X0 (σ y)
                   grind)
                | exact superpose b16e4404 b16e797
                | (have j0 := b16e797 (σ y)
                   grind)
                | exact resolve b16e797 b16e4404
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e797 b16e4404
              have b16e9229 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have j0 := b16e9169 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9169
              have b16e9238 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have i₁ := b16e9216 X0
                   have i₂ := b16e71 y
                   grind)
                | exact superpose b16e71 b16e9216
                | (have j0 := b16e9216 X0
                   grind)
                | exact resolve b16e9216 b16e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9216
              have b16e9256 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b16e9229 X0 X1
                   have i₂ := b16e460 X1 X0
                   grind)
                | exact superpose b16e460 b16e9229
                | (have j0 := b16e9229 X0 X1
                   grind)
                | exact resolve b16e9229 b16e460
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e460 b16e9229
              have b16e9308 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have i₁ := b16e9238 X0
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e9238
                | (have j0 := b16e9238 X0
                   grind)
                | exact resolve b16e9238 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9238
              have b16e9309 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have j0 := b16e9308 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9308
              have b16e9324 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have j0 := b16e9256 X0 X1
                   have j1 := b16e9185 X0 X1
                   grind)
                | (have r₁ := b16e9256 X0 X1
                   have r₂ := b16e9185 X0 X1
                   grind)
                | exact resolve b16e9256 b16e9185
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9185 b16e9256
              have b16e9348 : ∀ X0 : G, (σ (M.op y y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b16e9309 X0
                   have i₂ := b16e71 y
                   grind)
                | exact superpose b16e71 b16e9309
                | exact resolve b16e9309 b16e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9309
              have b16e9361 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b16e9348 x
                   have i₂ := b16e9324 (σ y) x
                   grind)
                | exact superpose b16e9324 b16e9348
                | exact resolve b16e9348 b16e9324
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9324 b16e9348
              have b16e9366 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b16e9361
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e9361
                | exact resolve b16e9361 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9361
              have b16e9368 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b16e9366
                   have r₂ := b16e5655
                   grind)
                | exact resolve b16e9366 b16e5655
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9366
              have b16e9426 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) := by
                first
                | (have i₁ := b16e3017 (σ y) (σ x)
                   have i₂ := b16e9368
                   grind)
                | exact superpose b16e9368 b16e3017
                | exact resolve b16e3017 b16e9368
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e3017
              have b16e9428 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) := by
                first
                | (have i₁ := b16e7791 (σ y) (σ x)
                   have i₂ := b16e9368
                   grind)
                | exact superpose b16e9368 b16e7791
                | exact resolve b16e7791 b16e9368
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e7791 b16e9368
              have b16e9432 : (σ y) = (M.op (σ x) (σ (M.op y y))) := by
                first
                | (have i₁ := b16e9428
                   have i₂ := b16e71 y
                   grind)
                | exact superpose b16e71 b16e9428
                | exact resolve b16e9428 b16e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9428
              have b16e9433 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op y y))) := by
                first
                | (have i₁ := b16e9426
                   have i₂ := b16e71 y
                   grind)
                | exact superpose b16e71 b16e9426
                | exact resolve b16e9426 b16e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e71 b16e9426
              have b16e9449 : (σ y) = (M.op (σ x) (σ (M.op x y))) := by
                first
                | (have i₁ := b16e9432
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e9432
                | exact resolve b16e9432 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9432
              have b16e9450 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
                first
                | (have i₁ := b16e9433
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e9433
                | exact resolve b16e9433 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9433
              have b16e9457 : (σ (M.op x y)) = (σ y) := by
                first
                | (have i₁ := b16e9450
                   have i₂ := b16e9449
                   grind)
                | exact superpose b16e9449 b16e9450
                | exact resolve b16e9450 b16e9449
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e9449 b16e9450
              have b16e9460 : False := by grind
              exact b16e9460
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b17e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b17e28 : (M.op x y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
              have b17e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                   have i₂ := b17e15 X0 X2 X3
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e37 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
                   have i₂ := b17e15 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b17e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e72 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
                intro X0
                first
                | (have i₁ := b17e30 X0 (τ X0)
                   have i₂ := b17e67 (τ X0)
                   grind)
                | exact superpose b17e67 b17e30
                | exact resolve b17e30 b17e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e30
              have b17e75 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b17e72 X0
                   have i₂ := b17e17 X0
                   grind)
                | exact superpose b17e17 b17e72
                | exact resolve b17e72 b17e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e72
              have b17e81 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b17e75 X0
                   have i₂ := b17e67 X0
                   grind)
                | exact superpose b17e67 b17e75
                | exact resolve b17e75 b17e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e67 b17e75
              have b17e104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e18 X0 X1
                   have i₂ := b17e20 X0 X1
                   grind)
                | (have i₁ := b17e18 X0 X0
                   have i₂ := b17e20 X0 X1
                   grind)
                | exact superpose b17e20 b17e18
                | (have j0 := b17e18 X0 X0
                   have j1 := b17e20 X0 X1
                   grind)
                | (have r₁ := b17e18 X0 X1
                   have r₂ := b17e20 X0 X1
                   grind)
                | (have r₁ := b17e18 X1 X1
                   have r₂ := b17e20 X1 X1
                   grind)
                | (have r₁ := b17e18 X0 X0
                   have r₂ := b17e20 X0 X0
                   grind)
                | exact resolve b17e18 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e112 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e19 X0 X1
                   have i₂ := b17e20 X0 X1
                   grind)
                | (have i₁ := b17e19 X0 X0
                   have i₂ := b17e20 X0 X1
                   grind)
                | exact superpose b17e20 b17e19
                | (have j0 := b17e19 X0 X1
                   have j1 := b17e20 X0 X1
                   grind)
                | (have r₁ := b17e19 X1 X1
                   have r₂ := b17e20 X1 X1
                   grind)
                | (have r₁ := b17e19 X0 X1
                   have r₂ := b17e20 X0 X1
                   grind)
                | (have r₁ := b17e19 X0 X0
                   have r₂ := b17e20 X0 X0
                   grind)
                | exact resolve b17e19 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b17e112 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e112
              have b17e125 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b17e124 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e124
              have b17e127 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b17e104 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e104
              have b17e128 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b17e127 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e127
              have b17e135 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b17e125 X0 X1
                   have j1 := b17e18 X0 X1
                   grind)
                | (have r₁ := b17e125 X0 X1
                   have r₂ := b17e18 X0 X1
                   grind)
                | (have r₁ := b17e125 X1 X1
                   have r₂ := b17e18 X1 X1
                   grind)
                | exact resolve b17e125 b17e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e125
              have b17e165 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e135 (σ X0) (σ X1)
                   have i₂ := b17e21 X0 X1
                   grind)
                | exact superpose b17e21 b17e135
                | exact resolve b17e135 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e135
              have b17e184 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b17e16 (M.op (τ X0) (τ X0))
                   have i₂ := b17e81 X0
                   grind)
                | exact superpose b17e81 b17e16
                | exact resolve b17e16 b17e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e81
              have b17e301 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op (M.op X2 X0) X0))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e37 (M.op X1 (M.op (M.op X2 X0) X0)) X1 X1
                   have i₂ := b17e15 X0 X1 X2
                   grind)
                | exact superpose b17e15 b17e37
                | exact resolve b17e37 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e375 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e36 X0 X2 X0 X1
                   have i₂ := b17e15 X0 X0 X1
                   grind)
                | exact superpose b17e15 b17e36
                | exact resolve b17e36 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e36
              have b17e411 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b17e375 X1 x X3
                   have i₂ := b17e375 X1 x X0
                   grind)
                | exact superpose b17e375 b17e375
                | exact resolve b17e375 b17e375
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e421 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X1 X1 x
                   have i₂ := b17e375 X1 x X0
                   grind)
                | exact superpose b17e375 b17e15
                | exact resolve b17e15 b17e375
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e428 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e37 X0 (M.op X2 X0) X2
                   have i₂ := b17e375 X0 X1 (M.op X2 X0)
                   grind)
                | exact superpose b17e375 b17e37
                | exact resolve b17e37 b17e375
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e375
              have b17e439 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e428 X0 X1 X2
                   have i₂ := b17e37 X0 X0 X1
                   grind)
                | exact superpose b17e37 b17e428
                | exact resolve b17e428 b17e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e428
              have b17e471 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
                intro X0
                first
                | (have i₁ := b17e421 X0 (M.op X0 X0)
                   have i₂ := b17e421 X0 X0
                   grind)
                | exact superpose b17e421 b17e421
                | exact resolve b17e421 b17e421
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e478 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e37 (M.op X0 (M.op X0 X1)) X1 X1
                   have i₂ := b17e421 X0 X1
                   grind)
                | exact superpose b17e421 b17e37
                | exact resolve b17e37 b17e421
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e482 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e478 X1 X0 X2
                   have i₂ := b17e421 X0 X1
                   grind)
                | exact superpose b17e421 b17e478
                | exact resolve b17e478 b17e421
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e478
              have b17e563 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e37 X0 X1 X0
                   have i₂ := b17e471 X0
                   grind)
                | exact superpose b17e471 b17e37
                | exact resolve b17e37 b17e471
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e564 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X0 X1 X0
                   have i₂ := b17e471 X0
                   grind)
                | exact superpose b17e471 b17e15
                | exact resolve b17e15 b17e471
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e577 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b17e421 (M.op X0 X0) X0
                   have i₂ := b17e471 X0
                   grind)
                | exact superpose b17e471 b17e421
                | exact resolve b17e421 b17e471
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e808 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b17e421 X1 (M.op X1 (M.op X0 X0))
                   have i₂ := b17e564 X0 X1
                   grind)
                | exact superpose b17e564 b17e421
                | exact resolve b17e421 b17e564
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e856 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X3 X0) X0)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e411 X1 (M.op X2 (M.op (M.op X3 X0) X0)) X2
                   have i₂ := b17e15 X0 X2 X3
                   grind)
                | exact superpose b17e15 b17e411
                | exact resolve b17e411 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e858 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e411 X1 (M.op X2 (M.op X0 X0)) X2
                   have i₂ := b17e564 X0 X2
                   grind)
                | exact superpose b17e564 b17e411
                | exact resolve b17e411 b17e564
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e859 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e411 X1 (M.op X2 (M.op X2 X0)) X0
                   have i₂ := b17e421 X2 X0
                   grind)
                | exact superpose b17e421 b17e411
                | exact resolve b17e411 b17e421
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e1046 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e439 (M.op X2 (M.op X2 X0)) X0 X1
                   have i₂ := b17e421 X2 X0
                   grind)
                | exact superpose b17e421 b17e439
                | exact resolve b17e439 b17e421
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e1105 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e471 X1
                   have i₂ := b17e439 X1 X0 X1
                   grind)
                | (have i₁ := b17e471 X1
                   have i₂ := b17e439 X1 X1 X0
                   grind)
                | exact superpose b17e439 b17e471
                | exact resolve b17e471 b17e439
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e439 b17e471
              have b17e1145 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) := by
                intro X0 X2
                first
                | (have i₁ := b17e1046 X0 x X2
                   have i₂ := b17e1105 x (M.op X2 (M.op X2 X0))
                   grind)
                | exact superpose b17e1105 b17e1046
                | exact resolve b17e1046 b17e1105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1046
              have b17e1171 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
                intro X0 X2
                first
                | (have i₁ := b17e1145 X0 X2
                   have i₂ := b17e421 X2 X0
                   grind)
                | exact superpose b17e421 b17e1145
                | exact resolve b17e1145 b17e421
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e421 b17e1145
              have b17e1688 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e482 (M.op X1 (M.op X0 X0)) X2 X1
                   have i₂ := b17e564 X0 X1
                   grind)
                | exact superpose b17e564 b17e482
                | exact resolve b17e482 b17e564
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e564
              have b17e1820 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b17e1688 X0 X1 x
                   have i₂ := b17e858 X0 x X1
                   grind)
                | exact superpose b17e858 b17e1688
                | exact resolve b17e1688 b17e858
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e858 b17e1688
              have b17e3333 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
                intro X0
                first
                | (have i₁ := b17e577 (τ X0)
                   have i₂ := b17e184 X0
                   grind)
                | exact superpose b17e184 b17e577
                | exact resolve b17e577 b17e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e577
              have b17e3384 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
                intro X0
                first
                | (have i₁ := b17e3333 X0
                   have i₂ := b17e184 (M.op X0 X0)
                   grind)
                | exact superpose b17e184 b17e3333
                | exact resolve b17e3333 b17e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e184 b17e3333
              have b17e3398 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
                intro X0
                first
                | (have i₁ := b17e3384 X0
                   have i₂ := b17e1820 X0 (M.op X0 X0)
                   grind)
                | exact superpose b17e1820 b17e3384
                | exact resolve b17e3384 b17e1820
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3384
              have b17e3411 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
                intro X0
                first
                | (have i₁ := b17e3398 X0
                   have i₂ := b17e1105 X0 X0
                   grind)
                | exact superpose b17e1105 b17e3398
                | exact resolve b17e3398 b17e1105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3398
              have b17e4417 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e563 X0 X1
                   have i₂ := b17e1820 X0 X1
                   grind)
                | (have i₁ := b17e563 X0 X0
                   have i₂ := b17e1820 X0 X0
                   grind)
                | exact superpose b17e1820 b17e563
                | exact resolve b17e563 b17e1820
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e563
              have b17e4523 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e1105 X1 (M.op X0 X1)
                   have i₂ := b17e1820 X1 X0
                   grind)
                | (have i₁ := b17e1105 X1 (M.op X0 X0)
                   have i₂ := b17e1820 X0 X1
                   grind)
                | exact superpose b17e1820 b17e1105
                | exact resolve b17e1105 b17e1820
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e4525 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b17e482 X1 X0 X0
                   have i₂ := b17e1820 (M.op X0 X1) X0
                   grind)
                | exact superpose b17e1820 b17e482
                | exact resolve b17e482 b17e1820
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e482
              have b17e4535 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X0 (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e4523 X0 X1
                   have i₂ := b17e808 X1 X0
                   grind)
                | exact superpose b17e808 b17e4523
                | exact resolve b17e4523 b17e808
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e808 b17e4523
              have b17e4776 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b17e22
                   have i₂ := b17e165 y x
                   grind)
                | exact superpose b17e165 b17e22
                | (have j1 := b17e165 y x
                   grind)
                | exact resolve b17e22 b17e165
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e165
              have b17e11288 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ (M.op X0 (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b17e3411 X1
                   have i₂ := b17e411 X1 X1 X0
                   grind)
                | (have i₁ := b17e3411 X1
                   have i₂ := b17e411 X0 X1 X1
                   grind)
                | exact superpose b17e411 b17e3411
                | exact resolve b17e3411 b17e411
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3411
              have b17e12491 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b17e11288 X0 (σ X0)
                   have i₂ := b17e16 X0
                   grind)
                | exact superpose b17e16 b17e11288
                | exact resolve b17e11288 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e11288
              have b17e12968 : ∀ X0 X1 X2 : G, (M.op X0 (τ (M.op X1 (M.op X1 (σ X0))))) = (M.op (M.op X2 (M.op X0 (τ (M.op X1 (M.op X1 (σ X0)))))) (τ (M.op X1 (M.op X1 (σ X0))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e37 (τ (M.op X1 (M.op X1 (σ X0)))) X1 X0
                   have i₂ := b17e12491 X0 X1
                   grind)
                | exact superpose b17e12491 b17e37
                | exact resolve b17e37 b17e12491
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e37
              have b17e13000 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op X1 (M.op X1 (σ X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b17e4525 X0 (τ (M.op X1 (M.op X1 (σ X0))))
                   have i₂ := b17e12491 X0 X1
                   grind)
                | exact superpose b17e12491 b17e4525
                | exact resolve b17e4525 b17e12491
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e4525
              have b17e13027 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e12968 X0 X1 X2
                   have i₂ := b17e12491 X0 X1
                   grind)
                | exact superpose b17e12491 b17e12968
                | exact resolve b17e12968 b17e12491
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e12968
              have b17e13791 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op (M.op X4 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b17e411 X3 (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X4 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))))
                   have i₂ := b17e301 X0 X1 X2 X4
                   grind)
                | exact superpose b17e301 b17e411
                | exact resolve b17e411 b17e301
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e301
              have b17e13822 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op X3 (M.op X3 (M.op X1 (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e13791 X0 X1 X2 X3 x
                   have i₂ := b17e1105 x (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))
                   grind)
                | exact superpose b17e1105 b17e13791
                | exact resolve b17e13791 b17e1105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e13791
              have b17e13917 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e13822 X0 X1 X2 x
                   have i₂ := b17e856 X0 x X1 X2
                   grind)
                | exact superpose b17e856 b17e13822
                | exact resolve b17e13822 b17e856
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e856 b17e13822
              have b17e13974 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X1 (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e13917 X0 X1 X2
                   have i₂ := b17e4535 X0 (M.op X1 (M.op (M.op X2 X0) X0))
                   grind)
                | exact superpose b17e4535 b17e13917
                | exact resolve b17e13917 b17e4535
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e13917
              have b17e14007 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e13974 X0 X1 X2
                   have i₂ := b17e4535 X1 (M.op (M.op X2 X0) X0)
                   grind)
                | exact superpose b17e4535 b17e13974
                | exact resolve b17e13974 b17e4535
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e13974
              have b17e14033 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op (M.op X2 X0) (M.op X0 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e14007 X0 X1 X2
                   have i₂ := b17e4535 (M.op X2 X0) X0
                   grind)
                | exact superpose b17e4535 b17e14007
                | exact resolve b17e14007 b17e4535
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e4535 b17e14007
              have b17e14051 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op X0 (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e14033 X0 X1 X2
                   have i₂ := b17e1820 X0 (M.op X2 X0)
                   grind)
                | exact superpose b17e1820 b17e14033
                | exact resolve b17e14033 b17e1820
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1820 b17e14033
              have b17e14059 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b17e14051 X0 X1 x
                   have i₂ := b17e1105 x X0
                   grind)
                | exact superpose b17e1105 b17e14051
                | exact resolve b17e14051 b17e1105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1105 b17e14051
              have b17e18410 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e859 X2 X1 X1
                   have i₂ := b17e411 X1 (M.op X1 X2) X0
                   grind)
                | (have i₁ := b17e859 X2 X1 X1
                   have i₂ := b17e411 X0 (M.op X1 X2) X1
                   grind)
                | exact superpose b17e411 b17e859
                | exact resolve b17e859 b17e411
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e411
              have b17e23263 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = (M.op (M.op X2 (M.op X2 X0)) (M.op X1 (M.op X0 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e14059 (M.op X2 (M.op X2 X0)) X1
                   have i₂ := b17e859 X0 (M.op X2 (M.op X2 X0)) X2
                   grind)
                | exact superpose b17e859 b17e14059
                | exact resolve b17e14059 b17e859
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e859 b17e14059
              have b17e26971 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e18410 X0 (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))
                   have i₂ := b17e1171 X0 X2
                   grind)
                | exact superpose b17e1171 b17e18410
                | exact resolve b17e18410 b17e1171
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1171 b17e18410
              have b17e46028 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 (M.op X2 X0)) (M.op X0 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e26971 X0 X1 (M.op X0 (M.op X2 X0))
                   have i₂ := b17e4417 X0 X2
                   grind)
                | exact superpose b17e4417 b17e26971
                | exact resolve b17e26971 b17e4417
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e26971
              have b17e46498 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X0)) (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e46028 X0 X1 X2
                   have i₂ := b17e23263 X0 (M.op X0 (M.op X2 X0)) X1
                   grind)
                | exact superpose b17e23263 b17e46028
                | exact resolve b17e46028 b17e23263
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e23263 b17e46028
              have b17e98380 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op X0 (M.op X0 (σ (σ X1))))))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b17e12491 X1 (σ X1)
                   have i₂ := b17e13000 (σ X1) X0
                   grind)
                | exact superpose b17e13000 b17e12491
                | exact resolve b17e12491 b17e13000
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e12491
              have b17e99839 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (τ (τ (M.op X0 (M.op X0 (σ (σ X1))))))) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e13027 X1 (σ X1) X2
                   have i₂ := b17e13000 (σ X1) X0
                   grind)
                | exact superpose b17e13000 b17e13027
                | exact resolve b17e13027 b17e13000
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e13000 b17e13027
              have b17e144501 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b17e4776
                   have i₂ := b17e128 y x
                   grind)
                | exact superpose b17e128 b17e4776
                | (have j1 := b17e128 y x
                   grind)
                | exact resolve b17e4776 b17e128
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e128 b17e4776
              have b17e144506 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
              clear b17e144501
              have b17e144507 : (σ (M.op x y)) = (σ y) := by
                first
                | (have r₁ := b17e144506
                   have r₂ := b17e28
                   grind)
                | exact resolve b17e144506 b17e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e144506
              have b17e144555 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (τ (τ (M.op X0 (M.op X0 (σ (σ y))))))) := by
                intro X0
                first
                | (have i₁ := b17e98380 X0 (M.op x y)
                   have i₂ := b17e144507
                   grind)
                | exact superpose b17e144507 b17e98380
                | exact resolve b17e98380 b17e144507
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e98380 b17e144507
              have b17e144556 : y = (M.op x y) := by
                first
                | (have i₁ := b17e144555 x
                   have i₂ := b17e99839 x y x
                   grind)
                | exact superpose b17e99839 b17e144555
                | exact resolve b17e144555 b17e99839
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e99839 b17e144555
              have b17e144693 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 y)) (M.op x y)) := by
                intro X0
                first
                | (have i₁ := b17e46498 y x X0
                   have i₂ := b17e144556
                   grind)
                | exact superpose b17e144556 b17e46498
                | exact resolve b17e46498 b17e144556
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46498
              have b17e144710 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 y)) y) := by
                intro X0
                first
                | (have i₁ := b17e144693 X0
                   have i₂ := b17e144556
                   grind)
                | exact superpose b17e144556 b17e144693
                | exact resolve b17e144693 b17e144556
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e144693
              have b17e144736 : y = (M.op y y) := by
                first
                | (have i₁ := b17e144710 x
                   have i₂ := b17e4417 y x
                   grind)
                | exact superpose b17e4417 b17e144710
                | exact resolve b17e144710 b17e4417
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e4417 b17e144710
              have b17e145337 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b17e28
                   have i₂ := b17e144736
                   grind)
                | exact superpose b17e144736 b17e28
                | exact resolve b17e28 b17e144736
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e144736
              have b17e145571 : False := by grind
              exact b17e145571
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b18e22 : (M.op x x) ≠ (M.op y x) := by grind
          have b18e23 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          have b18e24 : (M.op y x) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b18e20
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e20
            | exact resolve b18e20 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e28 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op y x) y))) := by
            intro X0
            first
            | (have i₁ := b18e13 y X0 y
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
               have i₂ := b18e13 X0 X2 X3
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e30 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
               have i₂ := b18e13 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e44 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b18e16 y X0
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e16
            | (have j0 := b18e16 y X0
               grind)
            | (have r₁ := b18e16 y x
               have r₂ := b18e24
               grind)
            | exact resolve b18e16 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e47 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b18e16 (σ x) (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e16
            | (have j0 := b18e16 (σ x) (σ x)
               grind)
            | (have r₁ := b18e16 (σ x) (σ y)
               have r₂ := b18e23
               grind)
            | exact resolve b18e16 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b18e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e49 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          clear b18e47
          have b18e51 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b18e49
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e49
            | exact resolve b18e49 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e49
          have b18e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b18e19 X0 X0
               have i₂ := b18e48 (σ X0)
               grind)
            | exact superpose b18e48 b18e19
            | exact resolve b18e19 b18e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b18e54 X0
               have i₂ := b18e48 X0
               grind)
            | exact superpose b18e48 b18e54
            | exact resolve b18e54 b18e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e48 b18e54
          have b18e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b18e16 X0 X1
               have i₂ := b18e18 X0 X1
               grind)
            | (have i₁ := b18e16 X0 X0
               have i₂ := b18e18 X0 X1
               grind)
            | exact superpose b18e18 b18e16
            | (have j0 := b18e16 X0 X0
               have j1 := b18e18 X0 X1
               grind)
            | (have r₁ := b18e16 X0 X1
               have r₂ := b18e18 X0 X1
               grind)
            | (have r₁ := b18e16 X1 X1
               have r₂ := b18e18 X1 X1
               grind)
            | (have r₁ := b18e16 X0 X0
               have r₂ := b18e18 X0 X0
               grind)
            | exact resolve b18e16 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e98 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b18e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b18e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e81
          have b18e103 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b18e102 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e102
          have b18e105 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b18e98 X0 X1
               have j1 := b18e16 X0 X1
               grind)
            | (have r₁ := b18e98 X0 X1
               have r₂ := b18e16 X0 X1
               grind)
            | (have r₁ := b18e98 X1 X1
               have r₂ := b18e16 X1 X1
               grind)
            | exact resolve b18e98 b18e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e98
          have b18e193 : (M.op x y) = (k y x) := by
            first
            | (have j0 := b18e44 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e44
          have b18e240 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b18e105 (σ y) (σ x)
               have i₂ := b18e51
               grind)
            | exact superpose b18e51 b18e105
            | (have j0 := b18e105 (σ y) (σ x)
               grind)
            | exact resolve b18e105 b18e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e51 b18e105
          have b18e268 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b18e240
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e240
            | exact resolve b18e240 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e240
          have b18e273 : (σ (k x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b18e268
               have i₂ := b18e59 x
               grind)
            | exact superpose b18e59 b18e268
            | exact resolve b18e268 b18e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e59 b18e268
          have b18e275 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b18e273
               have i₂ := b18e19 y x
               grind)
            | exact superpose b18e19 b18e273
            | exact resolve b18e273 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e273
          have b18e276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b18e275
               have i₂ := b18e193
               grind)
            | exact superpose b18e193 b18e275
            | exact resolve b18e275 b18e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e193 b18e275
          have b18e277 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (k x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b18e276
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e276
            | exact resolve b18e276 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e276
          have b18e278 : (σ (k x y)) ≠ (σ (M.op x x)) := by
            first
            | (have r₁ := b18e277
               have r₂ := b18e25
               grind)
            | exact resolve b18e277 b18e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e25 b18e277
          have b18e279 : (σ (M.op x x)) ≠ (σ (M.op y x)) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b18e278
               have i₂ := b18e103 x y
               grind)
            | exact superpose b18e103 b18e278
            | (have j1 := b18e103 x y
               grind)
            | exact resolve b18e278 b18e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e103 b18e278
          have b18e283 : (σ (M.op x x)) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b18e279
               have r₂ := b18e22
               grind)
            | exact resolve b18e279 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e279
          have b18e460 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e29 X0 X2 X0 X1
               have i₂ := b18e13 X0 X0 X1
               grind)
            | exact superpose b18e13 b18e29
            | exact resolve b18e29 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e29
          have b18e555 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X1 X1 x
               have i₂ := b18e460 X1 x X0
               grind)
            | exact superpose b18e460 b18e13
            | exact resolve b18e13 b18e460
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e626 : y = (M.op y (M.op y (M.op y x))) := by
            first
            | (have i₁ := b18e555 y y
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e555
            | exact resolve b18e555 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e638 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e30 (M.op X0 (M.op X0 X1)) X1 X1
               have i₂ := b18e555 X0 X1
               grind)
            | exact superpose b18e555 b18e30
            | exact resolve b18e30 b18e555
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e643 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e638 X1 X0 X2
               have i₂ := b18e555 X0 X1
               grind)
            | exact superpose b18e555 b18e638
            | exact resolve b18e638 b18e555
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e638
          have b18e719 : (M.op y x) = (M.op (M.op y x) y) := by
            first
            | (have i₁ := b18e555 y (M.op y x)
               have i₂ := b18e626
               grind)
            | exact superpose b18e626 b18e555
            | exact resolve b18e555 b18e626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e555 b18e626
          have b18e1037 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op y x))) := by
            intro X0
            first
            | (have i₁ := b18e28 X0
               have i₂ := b18e719
               grind)
            | exact superpose b18e719 b18e28
            | exact resolve b18e28 b18e719
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e28 b18e719
          have b18e1278 : ∀ X0 : G, y = (M.op (M.op y x) (M.op (M.op X0 (M.op y x)) (M.op y x))) := by
            intro X0
            first
            | (have i₁ := b18e460 (M.op y x) X0 x
               have i₂ := b18e1037 x
               grind)
            | exact superpose b18e1037 b18e460
            | exact resolve b18e460 b18e1037
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e460
          have b18e1281 : ∀ X0 : G, (M.op y (M.op y x)) = (M.op (M.op X0 (M.op y x)) (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b18e30 (M.op y x) (M.op X0 (M.op y x)) X0
               have i₂ := b18e1037 (M.op X0 (M.op y x))
               grind)
            | exact superpose b18e1037 b18e30
            | exact resolve b18e30 b18e1037
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e30 b18e1037
          have b18e1299 : y = (M.op (M.op y x) (M.op y (M.op y x))) := by
            first
            | (have i₁ := b18e1278 x
               have i₂ := b18e1281 x
               grind)
            | exact superpose b18e1281 b18e1278
            | exact resolve b18e1278 b18e1281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1278 b18e1281
          have b18e1304 : x = y := by
            first
            | (have i₁ := b18e1299
               have i₂ := b18e643 x y y
               grind)
            | exact superpose b18e643 b18e1299
            | exact resolve b18e1299 b18e643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e643 b18e1299
          have b18e1556 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b18e283
               have i₂ := b18e1304
               grind)
            | exact superpose b18e1304 b18e283
            | exact resolve b18e283 b18e1304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e283 b18e1304
          have b18e1560 : False := by grind
          exact b18e1560
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b19e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b19e23 : (M.op x x) ≠ (M.op y x) := by grind
            have b19e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            have b19e25 : (M.op y x) ≠ (M.op y y) := by grind
            have b19e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e27 : (M.op x y) ≠ (M.op y x) := by
              first
              | (have i₁ := b19e25
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e25
              | exact resolve b19e25 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b19e21
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e21
              | exact resolve b19e21 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b19e14 X0 X2 X3
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e37 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
                 have i₂ := b19e14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b19e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b19e20 X0 X0
                 have i₂ := b19e59 (σ X0)
                 grind)
              | exact superpose b19e59 b19e20
              | exact resolve b19e20 b19e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b19e65 X0
                 have i₂ := b19e59 X0
                 grind)
              | exact superpose b19e59 b19e65
              | exact resolve b19e65 b19e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e59 b19e65
            have b19e78 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (M.op y X0) ∨ y = (k y X0) := by
              intro X0
              first
              | (have i₁ := b19e18 y x
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e18
              | (have j0 := b19e18 y X0
                 grind)
              | (have r₁ := b19e18 y x
                 have r₂ := b19e26
                 grind)
              | exact resolve b19e18 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e96 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              first
              | (have i₁ := b19e17 X0 X1
                 have i₂ := b19e19 X0 X1
                 grind)
              | (have i₁ := b19e17 X0 X0
                 have i₂ := b19e19 X0 X1
                 grind)
              | exact superpose b19e19 b19e17
              | (have j0 := b19e17 X0 X0
                 have j1 := b19e19 X0 X1
                 grind)
              | (have r₁ := b19e17 X0 X1
                 have r₂ := b19e19 X0 X1
                 grind)
              | (have r₁ := b19e17 X1 X1
                 have r₂ := b19e19 X1 X1
                 grind)
              | (have r₁ := b19e17 X0 X0
                 have r₂ := b19e19 X0 X0
                 grind)
              | exact resolve b19e17 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e118 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
              intro X0 X1
              first
              | (have j0 := b19e96 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e96
            have b19e119 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
              intro X0 X1
              first
              | (have j0 := b19e118 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e118
            have b19e195 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e20 X1 X0
                 have i₂ := b19e119 (σ X1) (σ X0)
                 grind)
              | exact superpose b19e119 b19e20
              | (have j1 := b19e119 (σ X1) (σ X0)
                 grind)
              | exact resolve b19e20 b19e119
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e119
            have b19e219 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e195 X0 X1
                 have i₂ := b19e72 X1
                 grind)
              | exact superpose b19e72 b19e195
              | (have j0 := b19e195 X0 X1
                 grind)
              | exact resolve b19e195 b19e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e195
            have b19e464 : (M.op x y) = (M.op y x) ∨ y = (k y x) := by
              first
              | (have j0 := b19e78 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e78
            have b19e465 : y = (k y x) := by
              first
              | (have r₁ := b19e464
                 have r₂ := b19e27
                 grind)
              | exact resolve b19e464 b19e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e27 b19e464
            have b19e498 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e36 X0 X2 X0 X1
                 have i₂ := b19e14 X0 X0 X1
                 grind)
              | exact superpose b19e14 b19e36
              | exact resolve b19e36 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e36
            have b19e553 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X1 X1 x
                 have i₂ := b19e498 X1 x X0
                 grind)
              | exact superpose b19e498 b19e14
              | exact resolve b19e14 b19e498
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e565 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e37 X0 (M.op X2 X0) X2
                 have i₂ := b19e498 X0 X1 (M.op X2 X0)
                 grind)
              | exact superpose b19e498 b19e37
              | exact resolve b19e37 b19e498
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e498
            have b19e575 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e565 X0 X1 X2
                 have i₂ := b19e37 X0 X0 X1
                 grind)
              | exact superpose b19e37 b19e565
              | exact resolve b19e565 b19e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e37 b19e565
            have b19e624 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
              intro X0
              first
              | (have i₁ := b19e553 X0 (M.op X0 X0)
                 have i₂ := b19e553 X0 X0
                 grind)
              | exact superpose b19e553 b19e553
              | exact resolve b19e553 b19e553
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e553
            have b19e2342 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 X1) := by
              intro X0 X1
              first
              | (have i₁ := b19e624 X1
                 have i₂ := b19e575 X1 X0 X1
                 grind)
              | (have i₁ := b19e624 X1
                 have i₂ := b19e575 X1 X1 X0
                 grind)
              | exact superpose b19e575 b19e624
              | exact resolve b19e624 b19e575
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e624
            have b19e5895 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b19e219 x y
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e219
              | exact resolve b19e219 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e219
            have b19e6077 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b19e5895
                 have i₂ := b19e465
                 grind)
              | exact superpose b19e465 b19e5895
              | exact resolve b19e5895 b19e465
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e465 b19e5895
            have b19e6129 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b19e6077
                 have i₂ := b19e72 x
                 grind)
              | exact superpose b19e72 b19e6077
              | exact resolve b19e6077 b19e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e72 b19e6077
            have b19e6157 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
              first
              | (have i₁ := b19e6129
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e6129
              | exact resolve b19e6129 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e6129
            have b19e6175 : (σ y) = (σ (M.op x x)) := by
              first
              | (have r₁ := b19e6157
                 have r₂ := b19e28
                 grind)
              | exact resolve b19e6157 b19e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e28 b19e6157
            have b19e6201 : (M.op x x) = (τ (σ y)) := by
              first
              | (have i₁ := b19e15 (M.op x x)
                 have i₂ := b19e6175
                 grind)
              | exact superpose b19e6175 b19e15
              | exact resolve b19e15 b19e6175
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e6175
            have b19e6245 : y = (M.op x x) := by
              first
              | (have i₁ := b19e6201
                 have i₂ := b19e15 y
                 grind)
              | exact superpose b19e15 b19e6201
              | exact resolve b19e6201 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e6201
            have b19e6452 : ∀ X0 : G, (M.op y x) = (M.op (M.op X0 x) x) := by
              intro X0
              first
              | (have i₁ := b19e575 x x X0
                 have i₂ := b19e6245
                 grind)
              | exact superpose b19e6245 b19e575
              | exact resolve b19e575 b19e6245
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e575 b19e6245
            have b19e6462 : (M.op x x) = (M.op y x) := by
              first
              | (have i₁ := b19e6452 x
                 have i₂ := b19e2342 x x
                 grind)
              | exact superpose b19e2342 b19e6452
              | exact resolve b19e6452 b19e2342
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2342 b19e6452
            have b19e6480 : False := by grind
            exact b19e6480
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b20e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b20e21
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e21
              | exact resolve b20e21 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b20e14 X0 X2 X3
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e35 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
                 have i₂ := b20e14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b20e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b20e20 X0 X0
                 have i₂ := b20e55 (σ X0)
                 grind)
              | exact superpose b20e55 b20e20
              | exact resolve b20e20 b20e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b20e59 X0
                 have i₂ := b20e55 X0
                 grind)
              | exact superpose b20e55 b20e59
              | exact resolve b20e59 b20e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e55 b20e59
            have b20e164 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b20e27
                 have i₂ := b20e66 x
                 grind)
              | exact superpose b20e66 b20e27
              | exact resolve b20e27 b20e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e27 b20e66
            have b20e436 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e34 X0 X2 X0 X1
                 have i₂ := b20e14 X0 X0 X1
                 grind)
              | exact superpose b20e14 b20e34
              | exact resolve b20e34 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e34
            have b20e476 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b20e436 X1 x X3
                 have i₂ := b20e436 X1 x X0
                 grind)
              | exact superpose b20e436 b20e436
              | exact resolve b20e436 b20e436
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e487 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b20e14 X1 X1 x
                 have i₂ := b20e436 X1 x X0
                 grind)
              | exact superpose b20e436 b20e14
              | exact resolve b20e14 b20e436
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e436
            have b20e550 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
              intro X0
              first
              | (have i₁ := b20e487 X0 (M.op X0 X0)
                 have i₂ := b20e487 X0 X0
                 grind)
              | exact superpose b20e487 b20e487
              | exact resolve b20e487 b20e487
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e557 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e35 (M.op X0 (M.op X0 X1)) X1 X1
                 have i₂ := b20e487 X0 X1
                 grind)
              | exact superpose b20e487 b20e35
              | exact resolve b20e35 b20e487
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35
            have b20e561 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e557 X1 X0 X2
                 have i₂ := b20e487 X0 X1
                 grind)
              | exact superpose b20e487 b20e557
              | exact resolve b20e557 b20e487
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e557
            have b20e592 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b20e14 X0 X1 X0
                 have i₂ := b20e550 X0
                 grind)
              | exact superpose b20e550 b20e14
              | exact resolve b20e14 b20e550
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e603 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b20e487 (M.op X0 X0) X0
                 have i₂ := b20e550 X0
                 grind)
              | exact superpose b20e550 b20e487
              | exact resolve b20e487 b20e550
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e487 b20e550
            have b20e970 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e476 X1 (M.op X2 (M.op X0 X0)) X2
                 have i₂ := b20e592 X0 X2
                 grind)
              | exact superpose b20e592 b20e476
              | exact resolve b20e476 b20e592
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e476
            have b20e1547 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e561 (M.op X1 (M.op X0 X0)) X2 X1
                 have i₂ := b20e592 X0 X1
                 grind)
              | exact superpose b20e592 b20e561
              | exact resolve b20e561 b20e592
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e592
            have b20e1678 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b20e1547 X0 X1 x
                 have i₂ := b20e970 X0 x X1
                 grind)
              | exact superpose b20e970 b20e1547
              | exact resolve b20e1547 b20e970
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e970 b20e1547
            have b20e4101 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b20e561 X1 X0 X0
                 have i₂ := b20e1678 (M.op X0 X1) X0
                 grind)
              | exact superpose b20e1678 b20e561
              | exact resolve b20e561 b20e1678
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e561 b20e1678
            have b20e5876 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
              first
              | (have i₁ := b20e4101 (σ x) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e4101
              | exact resolve b20e4101 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e4101
            have b20e5961 : (σ x) = (σ y) := by
              first
              | (have i₁ := b20e5876
                 have i₂ := b20e603 (σ x)
                 grind)
              | exact superpose b20e603 b20e5876
              | exact resolve b20e5876 b20e603
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e603 b20e5876
            have b20e6195 : y = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 y
                 have i₂ := b20e5961
                 grind)
              | exact superpose b20e5961 b20e15
              | exact resolve b20e15 b20e5961
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e5961
            have b20e6230 : x = y := by
              first
              | (have i₁ := b20e6195
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e6195
              | exact resolve b20e6195 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e6195
            have b20e6614 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b20e164
                 have i₂ := b20e6230
                 grind)
              | exact superpose b20e6230 b20e164
              | exact resolve b20e164 b20e6230
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e164 b20e6230
            have b20e6615 : False := by grind
            exact b20e6615
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : (M.op x y) ≠ (M.op x x) := by grind
            have b21e23 : (M.op x x) ≠ (M.op y x) := by grind
            have b21e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
            have b21e25 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b21e14 X0 X2 X3
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e74 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b21e76 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b21e74
            have b21e77 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e76
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e76 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e76
            have b21e78 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e77
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e77
              | exact resolve b21e77 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e77
            have b21e82 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e78
                 grind)
              | exact superpose b21e78 b21e15
              | exact resolve b21e15 b21e78
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e78
            have b21e83 : x = (k x y) := by
              first
              | (have i₁ := b21e82
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e82
              | exact resolve b21e82 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e82
            have b21e145 : x = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e83
                 grind)
              | exact superpose b21e83 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e83
            have b21e146 : x = (M.op y x) ∨ (M.op x x) = (M.op y x) := by
              first
              | (have r₁ := b21e145
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e145 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e145
            have b21e148 : x = (M.op y x) := by
              first
              | (have r₁ := b21e146
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e146 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e146
            have b21e167 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b21e23
                 have i₂ := b21e148
                 grind)
              | exact superpose b21e148 b21e23
              | exact resolve b21e23 b21e148
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e399 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e30 X0 X2 X0 X1
                 have i₂ := b21e14 X0 X0 X1
                 grind)
              | exact superpose b21e14 b21e30
              | exact resolve b21e30 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e30
            have b21e1288 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X1 X1 x
                 have i₂ := b21e399 X1 x X0
                 grind)
              | exact superpose b21e399 b21e14
              | exact resolve b21e14 b21e399
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e399
            have b21e1733 : x = (M.op x (M.op y x)) := by
              first
              | (have i₁ := b21e1288 y x
                 have i₂ := b21e148
                 grind)
              | exact superpose b21e148 b21e1288
              | exact resolve b21e1288 b21e148
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1288
            have b21e1778 : x = (M.op x x) := by
              first
              | (have i₁ := b21e1733
                 have i₂ := b21e148
                 grind)
              | exact superpose b21e148 b21e1733
              | exact resolve b21e1733 b21e148
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e148 b21e1733
            have b21e1792 : False := by grind
            exact b21e1792
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : (M.op x y) ≠ (M.op x x) := by grind
              have b22e24 : (M.op x x) ≠ (M.op y x) := by grind
              have b22e25 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
              have b22e26 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b22e15 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                   have i₂ := b22e15 X0 X2 X3
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e93 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b22e19 (σ x) (σ y)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e19
                | (have j0 := b22e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b22e19 (σ x) (σ y)
                   have r₂ := b22e26
                   grind)
                | exact resolve b22e19 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e95 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b22e93
              have b22e96 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e95
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e95 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e95
              have b22e97 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b22e96
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e96
                | exact resolve b22e96 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e96
              have b22e102 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e97
                   grind)
                | exact superpose b22e97 b22e16
                | exact resolve b22e16 b22e97
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e97
              have b22e103 : x = (k x y) := by
                first
                | (have i₁ := b22e102
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e102
                | exact resolve b22e102 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e102
              have b22e169 : x = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e103
                   grind)
                | exact superpose b22e103 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e103
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e103
              have b22e170 : x = (M.op y x) ∨ (M.op x x) = (M.op y x) := by
                first
                | (have r₁ := b22e169
                   have r₂ := b22e23
                   grind)
                | exact resolve b22e169 b22e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e169
              have b22e172 : x = (M.op y x) := by
                first
                | (have r₁ := b22e170
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e170 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e170
              have b22e185 : x ≠ (M.op x x) := by
                first
                | (have i₁ := b22e24
                   have i₂ := b22e172
                   grind)
                | exact superpose b22e172 b22e24
                | exact resolve b22e24 b22e172
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e347 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e37 X0 X2 X0 X1
                   have i₂ := b22e15 X0 X0 X1
                   grind)
                | exact superpose b22e15 b22e37
                | exact resolve b22e37 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e37
              have b22e926 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X1 X1 x
                   have i₂ := b22e347 X1 x X0
                   grind)
                | exact superpose b22e347 b22e15
                | exact resolve b22e15 b22e347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e347
              have b22e1091 : x = (M.op x (M.op y x)) := by
                first
                | (have i₁ := b22e926 y x
                   have i₂ := b22e172
                   grind)
                | exact superpose b22e172 b22e926
                | exact resolve b22e926 b22e172
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e926
              have b22e1128 : x = (M.op x x) := by
                first
                | (have i₁ := b22e1091
                   have i₂ := b22e172
                   grind)
                | exact superpose b22e172 b22e1091
                | exact resolve b22e1091 b22e172
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e172 b22e1091
              have b22e1138 : False := by grind
              exact b22e1138
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : (M.op x y) ≠ (M.op x x) := by grind
              have b23e24 : (M.op x x) ≠ (M.op y x) := by grind
              have b23e25 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
              have b23e26 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                   have i₂ := b23e15 X0 X2 X3
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e86 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b23e19 (σ x) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e19
                | (have j0 := b23e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b23e19 (σ x) (σ y)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e19 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e88 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b23e86
              have b23e89 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e88
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e88 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e88
              have b23e90 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b23e89
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e89
                | exact resolve b23e89 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e89
              have b23e95 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e90
                   grind)
                | exact superpose b23e90 b23e16
                | exact resolve b23e16 b23e90
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e90
              have b23e96 : x = (k x y) := by
                first
                | (have i₁ := b23e95
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e95
                | exact resolve b23e95 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e95
              have b23e162 : x = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e96
                   grind)
                | exact superpose b23e96 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e96
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e96
              have b23e163 : x = (M.op y x) ∨ (M.op x x) = (M.op y x) := by
                first
                | (have r₁ := b23e162
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e162 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e162
              have b23e165 : x = (M.op y x) := by
                first
                | (have r₁ := b23e163
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e163 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e163
              have b23e177 : x ≠ (M.op x x) := by
                first
                | (have i₁ := b23e24
                   have i₂ := b23e165
                   grind)
                | exact superpose b23e165 b23e24
                | exact resolve b23e24 b23e165
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e313 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e35 X0 X2 X0 X1
                   have i₂ := b23e15 X0 X0 X1
                   grind)
                | exact superpose b23e15 b23e35
                | exact resolve b23e35 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e35
              have b23e952 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X1 X1 x
                   have i₂ := b23e313 X1 x X0
                   grind)
                | exact superpose b23e313 b23e15
                | exact resolve b23e15 b23e313
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e313
              have b23e1094 : x = (M.op x (M.op y x)) := by
                first
                | (have i₁ := b23e952 y x
                   have i₂ := b23e165
                   grind)
                | exact superpose b23e165 b23e952
                | exact resolve b23e952 b23e165
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e952
              have b23e1133 : x = (M.op x x) := by
                first
                | (have i₁ := b23e1094
                   have i₂ := b23e165
                   grind)
                | exact superpose b23e165 b23e1094
                | exact resolve b23e1094 b23e165
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e165 b23e1094
              have b23e1144 : False := by grind
              exact b23e1144
        · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b24e25 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
            have b24e26 : (M.op y x) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e29 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op (M.op y x) y))) := by
              intro X0
              first
              | (have i₁ := b24e14 y X0 y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                 have i₂ := b24e14 X0 X2 X3
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e31 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
                 have i₂ := b24e14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e481 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e30 X0 X2 X0 X1
                 have i₂ := b24e14 X0 X0 X1
                 grind)
              | exact superpose b24e14 b24e30
              | exact resolve b24e30 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e30
            have b24e534 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 X1 x
                 have i₂ := b24e481 X1 x X0
                 grind)
              | exact superpose b24e481 b24e14
              | exact resolve b24e14 b24e481
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e596 : y = (M.op y (M.op y (M.op y x))) := by
              first
              | (have i₁ := b24e534 y y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e534
              | exact resolve b24e534 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e609 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e31 (M.op X0 (M.op X0 X1)) X1 X1
                 have i₂ := b24e534 X0 X1
                 grind)
              | exact superpose b24e534 b24e31
              | exact resolve b24e31 b24e534
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e614 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e609 X1 X0 X2
                 have i₂ := b24e534 X0 X1
                 grind)
              | exact superpose b24e534 b24e609
              | exact resolve b24e609 b24e534
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e609
            have b24e637 : (M.op y x) = (M.op (M.op y x) y) := by
              first
              | (have i₁ := b24e534 y (M.op y x)
                 have i₂ := b24e596
                 grind)
              | exact superpose b24e596 b24e534
              | exact resolve b24e534 b24e596
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e534 b24e596
            have b24e1018 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op y x))) := by
              intro X0
              first
              | (have i₁ := b24e29 X0
                 have i₂ := b24e637
                 grind)
              | exact superpose b24e637 b24e29
              | exact resolve b24e29 b24e637
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e29 b24e637
            have b24e1187 : ∀ X0 : G, y = (M.op (M.op y x) (M.op (M.op X0 (M.op y x)) (M.op y x))) := by
              intro X0
              first
              | (have i₁ := b24e481 (M.op y x) X0 x
                 have i₂ := b24e1018 x
                 grind)
              | exact superpose b24e1018 b24e481
              | exact resolve b24e481 b24e1018
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e481
            have b24e1190 : ∀ X0 : G, (M.op y (M.op y x)) = (M.op (M.op X0 (M.op y x)) (M.op y x)) := by
              intro X0
              first
              | (have i₁ := b24e31 (M.op y x) (M.op X0 (M.op y x)) X0
                 have i₂ := b24e1018 (M.op X0 (M.op y x))
                 grind)
              | exact superpose b24e1018 b24e31
              | exact resolve b24e31 b24e1018
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e31 b24e1018
            have b24e1206 : y = (M.op (M.op y x) (M.op y (M.op y x))) := by
              first
              | (have i₁ := b24e1187 x
                 have i₂ := b24e1190 x
                 grind)
              | exact superpose b24e1190 b24e1187
              | exact resolve b24e1187 b24e1190
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1187 b24e1190
            have b24e1211 : x = y := by
              first
              | (have i₁ := b24e1206
                 have i₂ := b24e614 x y y
                 grind)
              | exact superpose b24e614 b24e1206
              | exact resolve b24e1206 b24e614
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e614 b24e1206
            have b24e1330 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b24e25
                 have i₂ := b24e1211
                 grind)
              | exact superpose b24e1211 b24e25
              | exact resolve b24e25 b24e1211
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1211
            have b24e1338 : False := by grind
            exact b24e1338
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b25e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e27 : (M.op y x) ≠ (M.op y y) := by grind
              have b25e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e29 : (M.op x y) ≠ (M.op y x) := by
                first
                | (have i₁ := b25e27
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e27
                | exact resolve b25e27 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                   have i₂ := b25e15 X0 X2 X3
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e38 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
                   have i₂ := b25e15 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b25e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b25e21 X0 X0
                   have i₂ := b25e70 (σ X0)
                   grind)
                | exact superpose b25e70 b25e21
                | exact resolve b25e21 b25e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e74 X0
                   have i₂ := b25e70 X0
                   grind)
                | exact superpose b25e70 b25e74
                | exact resolve b25e74 b25e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e70 b25e74
              have b25e91 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (M.op y X0) ∨ y = (k y X0) := by
                intro X0
                first
                | (have i₁ := b25e19 y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e19
                | (have j0 := b25e19 y X0
                   grind)
                | (have r₁ := b25e19 y x
                   have r₂ := b25e28
                   grind)
                | exact resolve b25e19 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e106 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X1) = (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e20 X0 X1
                   have i₂ := b25e20 X0 X1
                   grind)
                | (have i₁ := b25e20 X0 X1
                   have i₂ := b25e20 X0 X0
                   grind)
                | exact superpose b25e20 b25e20
                | (have j0 := b25e20 X1 X0
                   have j1 := b25e20 X1 X0
                   grind)
                | exact resolve b25e20 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e118 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b25e18 X0 X1
                   have i₂ := b25e20 X0 X1
                   grind)
                | (have i₁ := b25e18 X0 X0
                   have i₂ := b25e20 X0 X1
                   grind)
                | exact superpose b25e20 b25e18
                | (have j0 := b25e18 X0 X0
                   have j1 := b25e20 X0 X1
                   grind)
                | (have r₁ := b25e18 X0 X1
                   have r₂ := b25e20 X0 X1
                   grind)
                | (have r₁ := b25e18 X1 X1
                   have r₂ := b25e20 X1 X1
                   grind)
                | (have r₁ := b25e18 X0 X0
                   have r₂ := b25e20 X0 X0
                   grind)
                | exact resolve b25e18 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e125 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e18 X1 X2
                   have i₂ := b25e20 X1 X0
                   grind)
                | (have i₁ := b25e18 X0 X1
                   have i₂ := b25e20 X0 X0
                   grind)
                | exact superpose b25e20 b25e18
                | (have j0 := b25e18 X1 X2
                   have j1 := b25e20 X1 X0
                   grind)
                | (have r₁ := b25e18 X0 X1
                   have r₂ := b25e20 X0 X1
                   grind)
                | (have r₁ := b25e18 X1 X1
                   have r₂ := b25e20 X1 X1
                   grind)
                | (have r₁ := b25e18 X0 X0
                   have r₂ := b25e20 X0 X0
                   grind)
                | exact resolve b25e18 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e127 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b25e19 X0 X1
                   have i₂ := b25e20 X0 X1
                   grind)
                | (have i₁ := b25e19 X0 X0
                   have i₂ := b25e20 X0 X1
                   grind)
                | exact superpose b25e20 b25e19
                | (have j0 := b25e19 X0 X1
                   have j1 := b25e20 X0 X1
                   grind)
                | (have r₁ := b25e19 X1 X1
                   have r₂ := b25e20 X1 X1
                   grind)
                | (have r₁ := b25e19 X0 X1
                   have r₂ := b25e20 X0 X1
                   grind)
                | (have r₁ := b25e19 X0 X0
                   have r₂ := b25e20 X0 X0
                   grind)
                | exact resolve b25e19 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e138 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b25e127 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e127
              have b25e139 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b25e138 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e138
              have b25e141 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b25e118 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e118
              have b25e142 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b25e141 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e141
              have b25e149 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b25e139 X0 X1
                   have j1 := b25e18 X0 X1
                   grind)
                | (have r₁ := b25e139 X0 X1
                   have r₂ := b25e18 X0 X1
                   grind)
                | (have r₁ := b25e139 X1 X1
                   have r₂ := b25e18 X1 X1
                   grind)
                | exact resolve b25e139 b25e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e139
              have b25e151 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have j0 := b25e125 X0 X1 X2
                   have j1 := b25e18 X1 X2
                   grind)
                | (have r₁ := b25e125 X1 X1 X2
                   have r₂ := b25e18 X1 X1
                   grind)
                | (have r₁ := b25e125 X1 X0 X2
                   have r₂ := b25e18 X0 X1
                   grind)
                | exact resolve b25e125 b25e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e125
              have b25e157 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X1) = (M.op X1 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have j0 := b25e106 X0 X1 X2
                   have j1 := b25e18 X1 X2
                   grind)
                | (have r₁ := b25e106 X1 X1 X1
                   have r₂ := b25e18 X1 X1
                   grind)
                | (have r₁ := b25e106 X0 X0 X0
                   have r₂ := b25e18 X0 X0
                   grind)
                | (have r₁ := b25e106 X0 X0 X1
                   have r₂ := b25e18 X0 X1
                   grind)
                | exact resolve b25e106 b25e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e106
              have b25e164 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have j0 := b25e157 X0 X1 X2
                   have j1 := b25e151 X2 X1 X2
                   grind)
                | (have r₁ := b25e157 X0 X2 X2
                   have r₂ := b25e151 X0 X2 X2
                   grind)
                | (have r₁ := b25e157 X1 X1 X0
                   have r₂ := b25e151 X0 X1 X1
                   grind)
                | (have r₁ := b25e157 X0 X1 X2
                   have r₂ := b25e151 X0 X1 X2
                   grind)
                | exact resolve b25e157 b25e151
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e151 b25e157
              have b25e189 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b25e149 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e149
              have b25e240 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X1 X0
                   have i₂ := b25e142 (σ X1) (σ X0)
                   grind)
                | exact superpose b25e142 b25e21
                | (have j1 := b25e142 (σ X1) (σ X0)
                   grind)
                | exact resolve b25e21 b25e142
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e142
              have b25e270 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e240 X0 X1
                   have i₂ := b25e83 X1
                   grind)
                | exact superpose b25e83 b25e240
                | (have j0 := b25e240 X0 X1
                   grind)
                | exact resolve b25e240 b25e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e240
              have b25e437 : (M.op x y) = (M.op y x) ∨ y = (k y x) := by
                first
                | (have j0 := b25e91 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e91
              have b25e438 : y = (k y x) := by
                first
                | (have r₁ := b25e437
                   have r₂ := b25e29
                   grind)
                | exact resolve b25e437 b25e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e29 b25e437
              have b25e469 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e37 X0 X2 X0 X1
                   have i₂ := b25e15 X0 X0 X1
                   grind)
                | exact superpose b25e15 b25e37
                | exact resolve b25e37 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e37
              have b25e508 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b25e469 X1 x X3
                   have i₂ := b25e469 X1 x X0
                   grind)
                | exact superpose b25e469 b25e469
                | exact resolve b25e469 b25e469
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e520 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X1 X1 x
                   have i₂ := b25e469 X1 x X0
                   grind)
                | exact superpose b25e469 b25e15
                | exact resolve b25e15 b25e469
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e469
              have b25e582 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
                intro X0
                first
                | (have i₁ := b25e520 X0 (M.op X0 X0)
                   have i₂ := b25e520 X0 X0
                   grind)
                | exact superpose b25e520 b25e520
                | exact resolve b25e520 b25e520
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e589 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e38 (M.op X0 (M.op X0 X1)) X1 X1
                   have i₂ := b25e520 X0 X1
                   grind)
                | exact superpose b25e520 b25e38
                | exact resolve b25e38 b25e520
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e594 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e589 X1 X0 X2
                   have i₂ := b25e520 X0 X1
                   grind)
                | exact superpose b25e520 b25e589
                | exact resolve b25e589 b25e520
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e589
              have b25e687 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b25e38 X0 X1 X0
                   have i₂ := b25e582 X0
                   grind)
                | exact superpose b25e582 b25e38
                | exact resolve b25e38 b25e582
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e38
              have b25e688 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X0 X1 X0
                   have i₂ := b25e582 X0
                   grind)
                | exact superpose b25e582 b25e15
                | exact resolve b25e15 b25e582
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e582
              have b25e870 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b25e22
                   have i₂ := b25e164 (σ x) (σ y) X0
                   grind)
                | (have i₁ := b25e22
                   have i₂ := b25e164 X0 (σ y) (σ x)
                   grind)
                | exact superpose b25e164 b25e22
                | (have j1 := b25e164 (σ x) (σ y) (σ x)
                   grind)
                | exact resolve b25e22 b25e164
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e164
              have b25e893 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b25e870 X0
                   have i₂ := b25e21 y x
                   grind)
                | exact superpose b25e21 b25e870
                | (have j0 := b25e870 X0
                   grind)
                | exact resolve b25e870 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e870
              have b25e925 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b25e893 X0
                   have i₂ := b25e438
                   grind)
                | exact superpose b25e438 b25e893
                | (have j0 := b25e893 X0
                   grind)
                | exact resolve b25e893 b25e438
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e893
              have b25e1272 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e508 X1 (M.op X2 (M.op X0 X0)) X2
                   have i₂ := b25e688 X0 X2
                   grind)
                | exact superpose b25e688 b25e508
                | exact resolve b25e508 b25e688
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e2993 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e594 (M.op X1 (M.op X0 X0)) X2 X1
                   have i₂ := b25e688 X0 X1
                   grind)
                | exact superpose b25e688 b25e594
                | exact resolve b25e594 b25e688
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e594
              have b25e3178 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e2993 X0 X1 x
                   have i₂ := b25e1272 X0 x X1
                   grind)
                | exact superpose b25e1272 b25e2993
                | exact resolve b25e2993 b25e1272
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1272 b25e2993
              have b25e3756 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e687 X1 X1
                   have i₂ := b25e508 X1 X1 X0
                   grind)
                | (have i₁ := b25e687 X1 X1
                   have i₂ := b25e508 X0 X1 X1
                   grind)
                | exact superpose b25e508 b25e687
                | exact resolve b25e687 b25e508
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e508 b25e687
              have b25e5936 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e270 x y
                   grind)
                | exact superpose b25e270 b25e22
                | (have j1 := b25e270 x y
                   grind)
                | exact resolve b25e22 b25e270
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e270
              have b25e6016 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b25e5936
                   have i₂ := b25e438
                   grind)
                | exact superpose b25e438 b25e5936
                | exact resolve b25e5936 b25e438
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e438 b25e5936
              have b25e6066 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have i₁ := b25e6016
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e6016
                | exact resolve b25e6016 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6016
              have b25e6098 : (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have r₁ := b25e6066
                   have r₂ := b25e22
                   grind)
                | exact resolve b25e6066 b25e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6066
              have b25e6605 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b25e688 X0 X1
                   have i₂ := b25e3178 X0 X1
                   grind)
                | (have i₁ := b25e688 X0 X0
                   have i₂ := b25e3178 X0 X0
                   grind)
                | exact superpose b25e3178 b25e688
                | exact resolve b25e688 b25e3178
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e688
              have b25e8194 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b25e19 X0 (M.op X1 (M.op X1 X0))
                   have i₂ := b25e3756 X1 X0
                   grind)
                | exact superpose b25e3756 b25e19
                | (have j0 := b25e19 X0 (M.op X1 (M.op X1 X0))
                   grind)
                | (have r₁ := b25e19 X1 (M.op X0 (M.op X0 X1))
                   have r₂ := b25e3756 X0 X1
                   grind)
                | exact resolve b25e19 b25e3756
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e8210 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b25e189 X0 (M.op X1 (M.op X1 X0))
                   have i₂ := b25e3756 X1 X0
                   grind)
                | exact superpose b25e3756 b25e189
                | (have j0 := b25e189 X0 X0
                   grind)
                | exact resolve b25e189 b25e3756
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e189
              have b25e8250 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have j0 := b25e8194 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e8194
              have b25e8274 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b25e8250 X0 X1
                   have i₂ := b25e520 X1 X0
                   grind)
                | exact superpose b25e520 b25e8250
                | (have j0 := b25e8250 X0 X1
                   grind)
                | exact resolve b25e8250 b25e520
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e520 b25e8250
              have b25e8337 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1
                first
                | (have j0 := b25e8274 X0 X1
                   have j1 := b25e8210 X0 X1
                   grind)
                | (have r₁ := b25e8274 X0 X1
                   have r₂ := b25e8210 X0 X1
                   grind)
                | exact resolve b25e8274 b25e8210
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e8210 b25e8274
              have b25e9503 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have i₁ := b25e925 (M.op X0 (M.op X0 (σ y)))
                   have i₂ := b25e3756 X0 (σ y)
                   grind)
                | exact superpose b25e3756 b25e925
                | (have j0 := b25e925 (σ y)
                   grind)
                | exact resolve b25e925 b25e3756
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e925 b25e3756
              have b25e9514 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have i₁ := b25e9503 X0
                   have i₂ := b25e83 y
                   grind)
                | exact superpose b25e83 b25e9503
                | (have j0 := b25e9503 X0
                   grind)
                | exact resolve b25e9503 b25e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9503
              have b25e9524 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have i₁ := b25e9514 X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e9514
                | (have j0 := b25e9514 X0
                   grind)
                | exact resolve b25e9514 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9514
              have b25e9525 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (M.op X0 (σ y)))) := by
                intro X0
                first
                | (have j0 := b25e9524 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9524
              have b25e9539 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e9525 x
                   have i₂ := b25e8337 (σ y) x
                   grind)
                | exact superpose b25e8337 b25e9525
                | exact resolve b25e9525 b25e8337
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e8337 b25e9525
              have b25e9551 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e9539
                   have i₂ := b25e83 y
                   grind)
                | exact superpose b25e83 b25e9539
                | exact resolve b25e9539 b25e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9539
              have b25e9560 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e9551
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e9551
                | exact resolve b25e9551 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9551
              have b25e9566 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b25e9560
                   have r₂ := b25e6098
                   grind)
                | exact resolve b25e9560 b25e6098
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9560
              have b25e9604 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) := by
                first
                | (have i₁ := b25e3178 (σ y) (σ x)
                   have i₂ := b25e9566
                   grind)
                | exact superpose b25e9566 b25e3178
                | exact resolve b25e3178 b25e9566
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3178
              have b25e9606 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) := by
                first
                | (have i₁ := b25e6605 (σ y) (σ x)
                   have i₂ := b25e9566
                   grind)
                | exact superpose b25e9566 b25e6605
                | exact resolve b25e6605 b25e9566
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6605 b25e9566
              have b25e9612 : (σ y) = (M.op (σ x) (σ (M.op y y))) := by
                first
                | (have i₁ := b25e9606
                   have i₂ := b25e83 y
                   grind)
                | exact superpose b25e83 b25e9606
                | exact resolve b25e9606 b25e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9606
              have b25e9613 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op y y))) := by
                first
                | (have i₁ := b25e9604
                   have i₂ := b25e83 y
                   grind)
                | exact superpose b25e83 b25e9604
                | exact resolve b25e9604 b25e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e83 b25e9604
              have b25e9630 : (σ y) = (M.op (σ x) (σ (M.op x y))) := by
                first
                | (have i₁ := b25e9612
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e9612
                | exact resolve b25e9612 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9612
              have b25e9631 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
                first
                | (have i₁ := b25e9613
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e9613
                | exact resolve b25e9613 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9613
              have b25e9638 : (σ (M.op x y)) = (σ y) := by
                first
                | (have i₁ := b25e9631
                   have i₂ := b25e9630
                   grind)
                | exact superpose b25e9630 b25e9631
                | exact resolve b25e9631 b25e9630
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e9630 b25e9631
              have b25e9642 : False := by grind
              exact b25e9642
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e28 : (M.op x y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e21
                | exact resolve b26e21 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
                   have i₂ := b26e15 X0 X2 X3
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e36 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
                   have i₂ := b26e15 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b26e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e71 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
                intro X0
                first
                | (have i₁ := b26e30 X0 (τ X0)
                   have i₂ := b26e66 (τ X0)
                   grind)
                | exact superpose b26e66 b26e30
                | exact resolve b26e30 b26e66
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30
              have b26e74 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b26e71 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e71
                | exact resolve b26e71 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e71
              have b26e80 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b26e74 X0
                   have i₂ := b26e66 X0
                   grind)
                | exact superpose b26e66 b26e74
                | exact resolve b26e74 b26e66
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e66 b26e74
              have b26e111 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e18 X0 X1
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e18 X0 X0
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e18
                | (have j0 := b26e18 X0 X0
                   have j1 := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e18 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e18 X1 X1
                   have r₂ := b26e20 X1 X1
                   grind)
                | (have r₁ := b26e18 X0 X0
                   have r₂ := b26e20 X0 X0
                   grind)
                | exact resolve b26e18 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e120 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e19 X0 X1
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e19 X0 X0
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e19
                | (have j0 := b26e19 X0 X1
                   have j1 := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e19 X1 X1
                   have r₂ := b26e20 X1 X1
                   grind)
                | (have r₁ := b26e19 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e19 X0 X0
                   have r₂ := b26e20 X0 X0
                   grind)
                | exact resolve b26e19 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e131 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b26e120 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e120
              have b26e132 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b26e131 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e131
              have b26e134 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b26e111 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e111
              have b26e135 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b26e134 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e134
              have b26e142 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b26e132 X0 X1
                   have j1 := b26e18 X0 X1
                   grind)
                | (have r₁ := b26e132 X0 X1
                   have r₂ := b26e18 X0 X1
                   grind)
                | (have r₁ := b26e132 X1 X1
                   have r₂ := b26e18 X1 X1
                   grind)
                | exact resolve b26e132 b26e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e132
              have b26e169 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e16 (M.op (τ X0) (τ X0))
                   have i₂ := b26e80 X0
                   grind)
                | exact superpose b26e80 b26e16
                | exact resolve b26e16 b26e80
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e80
              have b26e176 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e142 (σ X0) (σ X1)
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e142
                | exact resolve b26e142 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e142
              have b26e318 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op (M.op X2 X0) X0))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e36 (M.op X1 (M.op (M.op X2 X0) X0)) X1 X1
                   have i₂ := b26e15 X0 X1 X2
                   grind)
                | exact superpose b26e15 b26e36
                | exact resolve b26e36 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e400 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 X0 X2 X0 X1
                   have i₂ := b26e15 X0 X0 X1
                   grind)
                | exact superpose b26e15 b26e35
                | exact resolve b26e35 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e35
              have b26e436 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e400 X1 x X3
                   have i₂ := b26e400 X1 x X0
                   grind)
                | exact superpose b26e400 b26e400
                | exact resolve b26e400 b26e400
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e447 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e15 X1 X1 x
                   have i₂ := b26e400 X1 x X0
                   grind)
                | exact superpose b26e400 b26e15
                | exact resolve b26e15 b26e400
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e457 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e36 X0 (M.op X2 X0) X2
                   have i₂ := b26e400 X0 X1 (M.op X2 X0)
                   grind)
                | exact superpose b26e400 b26e36
                | exact resolve b26e36 b26e400
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e400
              have b26e465 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e457 X0 X1 X2
                   have i₂ := b26e36 X0 X0 X1
                   grind)
                | exact superpose b26e36 b26e457
                | exact resolve b26e457 b26e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e457
              have b26e501 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
                intro X0
                first
                | (have i₁ := b26e447 X0 (M.op X0 X0)
                   have i₂ := b26e447 X0 X0
                   grind)
                | exact superpose b26e447 b26e447
                | exact resolve b26e447 b26e447
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e508 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e36 (M.op X0 (M.op X0 X1)) X1 X1
                   have i₂ := b26e447 X0 X1
                   grind)
                | exact superpose b26e447 b26e36
                | exact resolve b26e36 b26e447
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e512 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e508 X1 X0 X2
                   have i₂ := b26e447 X0 X1
                   grind)
                | exact superpose b26e447 b26e508
                | exact resolve b26e508 b26e447
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e508
              have b26e539 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e36 X0 X1 X0
                   have i₂ := b26e501 X0
                   grind)
                | exact superpose b26e501 b26e36
                | exact resolve b26e36 b26e501
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e540 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e15 X0 X1 X0
                   have i₂ := b26e501 X0
                   grind)
                | exact superpose b26e501 b26e15
                | exact resolve b26e15 b26e501
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e551 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e447 (M.op X0 X0) X0
                   have i₂ := b26e501 X0
                   grind)
                | exact superpose b26e501 b26e447
                | exact resolve b26e447 b26e501
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e640 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e447 X1 (M.op X1 (M.op X0 X0))
                   have i₂ := b26e540 X0 X1
                   grind)
                | exact superpose b26e540 b26e447
                | exact resolve b26e447 b26e540
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e891 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X3 X0) X0)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e436 X1 (M.op X2 (M.op (M.op X3 X0) X0)) X2
                   have i₂ := b26e15 X0 X2 X3
                   grind)
                | exact superpose b26e15 b26e436
                | exact resolve b26e436 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e894 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e436 X1 (M.op X2 (M.op X0 X0)) X2
                   have i₂ := b26e540 X0 X2
                   grind)
                | exact superpose b26e540 b26e436
                | exact resolve b26e436 b26e540
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e895 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e436 X1 (M.op X2 (M.op X2 X0)) X0
                   have i₂ := b26e447 X2 X0
                   grind)
                | exact superpose b26e447 b26e436
                | exact resolve b26e436 b26e447
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1026 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e465 (M.op X2 (M.op X2 X0)) X0 X1
                   have i₂ := b26e447 X2 X0
                   grind)
                | exact superpose b26e447 b26e465
                | exact resolve b26e465 b26e447
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1083 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e501 X1
                   have i₂ := b26e465 X1 X0 X1
                   grind)
                | (have i₁ := b26e501 X1
                   have i₂ := b26e465 X1 X1 X0
                   grind)
                | exact superpose b26e465 b26e501
                | exact resolve b26e501 b26e465
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e465 b26e501
              have b26e1124 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) := by
                intro X0 X2
                first
                | (have i₁ := b26e1026 X0 x X2
                   have i₂ := b26e1083 x (M.op X2 (M.op X2 X0))
                   grind)
                | exact superpose b26e1083 b26e1026
                | exact resolve b26e1026 b26e1083
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1026
              have b26e1152 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
                intro X0 X2
                first
                | (have i₁ := b26e1124 X0 X2
                   have i₂ := b26e447 X2 X0
                   grind)
                | exact superpose b26e447 b26e1124
                | exact resolve b26e1124 b26e447
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e447 b26e1124
              have b26e1426 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e512 (M.op X1 (M.op X0 X0)) X2 X1
                   have i₂ := b26e540 X0 X1
                   grind)
                | exact superpose b26e540 b26e512
                | exact resolve b26e512 b26e540
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e540
              have b26e1550 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e1426 X0 X1 x
                   have i₂ := b26e894 X0 x X1
                   grind)
                | exact superpose b26e894 b26e1426
                | exact resolve b26e1426 b26e894
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e894 b26e1426
              have b26e2230 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
                intro X0
                first
                | (have i₁ := b26e551 (τ X0)
                   have i₂ := b26e169 X0
                   grind)
                | exact superpose b26e169 b26e551
                | exact resolve b26e551 b26e169
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e551
              have b26e2277 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
                intro X0
                first
                | (have i₁ := b26e2230 X0
                   have i₂ := b26e169 (M.op X0 X0)
                   grind)
                | exact superpose b26e169 b26e2230
                | exact resolve b26e2230 b26e169
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e169 b26e2230
              have b26e2291 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
                intro X0
                first
                | (have i₁ := b26e2277 X0
                   have i₂ := b26e1550 X0 (M.op X0 X0)
                   grind)
                | exact superpose b26e1550 b26e2277
                | exact resolve b26e2277 b26e1550
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2277
              have b26e2304 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
                intro X0
                first
                | (have i₁ := b26e2291 X0
                   have i₂ := b26e1083 X0 X0
                   grind)
                | exact superpose b26e1083 b26e2291
                | exact resolve b26e2291 b26e1083
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2291
              have b26e3699 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e539 X0 X1
                   have i₂ := b26e1550 X0 X1
                   grind)
                | (have i₁ := b26e539 X0 X0
                   have i₂ := b26e1550 X0 X0
                   grind)
                | exact superpose b26e1550 b26e539
                | exact resolve b26e539 b26e1550
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e539
              have b26e3801 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e1083 X1 (M.op X0 X1)
                   have i₂ := b26e1550 X1 X0
                   grind)
                | (have i₁ := b26e1083 X1 (M.op X0 X0)
                   have i₂ := b26e1550 X0 X1
                   grind)
                | exact superpose b26e1550 b26e1083
                | exact resolve b26e1083 b26e1550
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e3803 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e512 X1 X0 X0
                   have i₂ := b26e1550 (M.op X0 X1) X0
                   grind)
                | exact superpose b26e1550 b26e512
                | exact resolve b26e512 b26e1550
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e512
              have b26e3808 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X0 (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e3801 X0 X1
                   have i₂ := b26e640 X1 X0
                   grind)
                | exact superpose b26e640 b26e3801
                | exact resolve b26e3801 b26e640
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e640 b26e3801
              have b26e5043 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e176 y x
                   grind)
                | exact superpose b26e176 b26e22
                | (have j1 := b26e176 y x
                   grind)
                | exact resolve b26e22 b26e176
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e176
              have b26e9390 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ (M.op X0 (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e2304 X1
                   have i₂ := b26e436 X1 X1 X0
                   grind)
                | (have i₁ := b26e2304 X1
                   have i₂ := b26e436 X0 X1 X1
                   grind)
                | exact superpose b26e436 b26e2304
                | exact resolve b26e2304 b26e436
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2304
              have b26e10760 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e9390 X0 (σ X0)
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e9390
                | exact resolve b26e9390 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e9390
              have b26e11286 : ∀ X0 X1 X2 : G, (M.op X0 (τ (M.op X1 (M.op X1 (σ X0))))) = (M.op (M.op X2 (M.op X0 (τ (M.op X1 (M.op X1 (σ X0)))))) (τ (M.op X1 (M.op X1 (σ X0))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e36 (τ (M.op X1 (M.op X1 (σ X0)))) X1 X0
                   have i₂ := b26e10760 X0 X1
                   grind)
                | exact superpose b26e10760 b26e36
                | exact resolve b26e36 b26e10760
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e36
              have b26e11316 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op X1 (M.op X1 (σ X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e3803 X0 (τ (M.op X1 (M.op X1 (σ X0))))
                   have i₂ := b26e10760 X0 X1
                   grind)
                | exact superpose b26e10760 b26e3803
                | exact resolve b26e3803 b26e10760
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3803
              have b26e11342 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e11286 X0 X1 X2
                   have i₂ := b26e10760 X0 X1
                   grind)
                | exact superpose b26e10760 b26e11286
                | exact resolve b26e11286 b26e10760
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11286
              have b26e13854 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op (M.op X4 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e436 X3 (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X4 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))))
                   have i₂ := b26e318 X0 X1 X2 X4
                   grind)
                | exact superpose b26e318 b26e436
                | exact resolve b26e436 b26e318
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e318
              have b26e13886 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op X3 (M.op X3 (M.op X1 (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e13854 X0 X1 X2 X3 x
                   have i₂ := b26e1083 x (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))
                   grind)
                | exact superpose b26e1083 b26e13854
                | exact resolve b26e13854 b26e1083
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e13854
              have b26e13975 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e13886 X0 X1 X2 x
                   have i₂ := b26e891 X0 x X1 X2
                   grind)
                | exact superpose b26e891 b26e13886
                | exact resolve b26e13886 b26e891
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e891 b26e13886
              have b26e14028 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X1 (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e13975 X0 X1 X2
                   have i₂ := b26e3808 X0 (M.op X1 (M.op (M.op X2 X0) X0))
                   grind)
                | exact superpose b26e3808 b26e13975
                | exact resolve b26e13975 b26e3808
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e13975
              have b26e14058 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e14028 X0 X1 X2
                   have i₂ := b26e3808 X1 (M.op (M.op X2 X0) X0)
                   grind)
                | exact superpose b26e3808 b26e14028
                | exact resolve b26e14028 b26e3808
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e14028
              have b26e14083 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op (M.op X2 X0) (M.op X0 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e14058 X0 X1 X2
                   have i₂ := b26e3808 (M.op X2 X0) X0
                   grind)
                | exact superpose b26e3808 b26e14058
                | exact resolve b26e14058 b26e3808
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3808 b26e14058
              have b26e14100 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op X0 (M.op (M.op X2 X0) X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e14083 X0 X1 X2
                   have i₂ := b26e1550 X0 (M.op X2 X0)
                   grind)
                | exact superpose b26e1550 b26e14083
                | exact resolve b26e14083 b26e1550
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1550 b26e14083
              have b26e14107 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e14100 X0 X1 x
                   have i₂ := b26e1083 x X0
                   grind)
                | exact superpose b26e1083 b26e14100
                | exact resolve b26e14100 b26e1083
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1083 b26e14100
              have b26e16858 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e895 X2 X1 X1
                   have i₂ := b26e436 X1 (M.op X1 X2) X0
                   grind)
                | (have i₁ := b26e895 X2 X1 X1
                   have i₂ := b26e436 X0 (M.op X1 X2) X1
                   grind)
                | exact superpose b26e436 b26e895
                | exact resolve b26e895 b26e436
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e436
              have b26e20385 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = (M.op (M.op X2 (M.op X2 X0)) (M.op X1 (M.op X0 X0))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e14107 (M.op X2 (M.op X2 X0)) X1
                   have i₂ := b26e895 X0 (M.op X2 (M.op X2 X0)) X2
                   grind)
                | exact superpose b26e895 b26e14107
                | exact resolve b26e14107 b26e895
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e895 b26e14107
              have b26e23148 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e16858 X0 (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))
                   have i₂ := b26e1152 X0 X2
                   grind)
                | exact superpose b26e1152 b26e16858
                | exact resolve b26e16858 b26e1152
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1152 b26e16858
              have b26e37471 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 (M.op X2 X0)) (M.op X0 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e23148 X0 X1 (M.op X0 (M.op X2 X0))
                   have i₂ := b26e3699 X0 X2
                   grind)
                | exact superpose b26e3699 b26e23148
                | exact resolve b26e23148 b26e3699
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e23148
              have b26e37899 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X0)) (M.op X1 (M.op X1 X0))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e37471 X0 X1 X2
                   have i₂ := b26e20385 X0 (M.op X0 (M.op X2 X0)) X1
                   grind)
                | exact superpose b26e20385 b26e37471
                | exact resolve b26e37471 b26e20385
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e20385 b26e37471
              have b26e88352 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op X0 (M.op X0 (σ (σ X1))))))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e10760 X1 (σ X1)
                   have i₂ := b26e11316 (σ X1) X0
                   grind)
                | exact superpose b26e11316 b26e10760
                | exact resolve b26e10760 b26e11316
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e10760
              have b26e90048 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (τ (τ (M.op X0 (M.op X0 (σ (σ X1))))))) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e11342 X1 (σ X1) X2
                   have i₂ := b26e11316 (σ X1) X0
                   grind)
                | exact superpose b26e11316 b26e11342
                | exact resolve b26e11342 b26e11316
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11316 b26e11342
              have b26e152555 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b26e5043
                   have i₂ := b26e135 y x
                   grind)
                | exact superpose b26e135 b26e5043
                | (have j1 := b26e135 y x
                   grind)
                | exact resolve b26e5043 b26e135
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e135 b26e5043
              have b26e152560 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
              clear b26e152555
              have b26e152561 : (σ (M.op x y)) = (σ y) := by
                first
                | (have r₁ := b26e152560
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e152560 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e152560
              have b26e152609 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (τ (τ (M.op X0 (M.op X0 (σ (σ y))))))) := by
                intro X0
                first
                | (have i₁ := b26e88352 X0 (M.op x y)
                   have i₂ := b26e152561
                   grind)
                | exact superpose b26e152561 b26e88352
                | exact resolve b26e88352 b26e152561
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e88352 b26e152561
              have b26e152610 : y = (M.op x y) := by
                first
                | (have i₁ := b26e152609 x
                   have i₂ := b26e90048 x y x
                   grind)
                | exact superpose b26e90048 b26e152609
                | exact resolve b26e152609 b26e90048
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e90048 b26e152609
              have b26e152749 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 y)) (M.op x y)) := by
                intro X0
                first
                | (have i₁ := b26e37899 y x X0
                   have i₂ := b26e152610
                   grind)
                | exact superpose b26e152610 b26e37899
                | exact resolve b26e37899 b26e152610
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e37899
              have b26e152765 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 y)) y) := by
                intro X0
                first
                | (have i₁ := b26e152749 X0
                   have i₂ := b26e152610
                   grind)
                | exact superpose b26e152610 b26e152749
                | exact resolve b26e152749 b26e152610
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e152749
              have b26e152791 : y = (M.op y y) := by
                first
                | (have i₁ := b26e152765 x
                   have i₂ := b26e3699 y x
                   grind)
                | exact superpose b26e3699 b26e152765
                | exact resolve b26e152765 b26e3699
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3699 b26e152765
              have b26e153425 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b26e28
                   have i₂ := b26e152791
                   grind)
                | exact superpose b26e152791 b26e28
                | exact resolve b26e28 b26e152791
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e152791
              have b26e153669 : False := by grind
              exact b26e153669

/-- `Equation778`: `x = y ◇ (z ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_x_pyx_Equation778 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law778 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law778.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
      · have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : (M.op x y) = (M.op x x) := by grind
        have b0e21 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e19
          | exact resolve b0e19 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e25 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e24
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e24
          | exact resolve b0e24 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24
        have b0e55 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b0e15 x y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e15
          | (have j0 := b0e15 x x
             grind)
          | (have r₁ := b0e15 x y
             have r₂ := b0e20
             grind)
          | exact resolve b0e15 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e58 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b0e15 (σ x) (σ y)
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e15
          | (have j0 := b0e15 (σ x) (σ x)
             grind)
          | (have r₁ := b0e15 (σ x) (σ y)
             have r₂ := b0e21
             grind)
          | exact resolve b0e15 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e60 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b0e58
        have b0e62 : (M.op x x) = (k x y) := by grind
        clear b0e55
        have b0e63 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b0e60
             have i₂ := b0e18 x y
             grind)
          | exact superpose b0e18 b0e60
          | exact resolve b0e60 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e60
        have b0e65 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b0e63
             have i₂ := b0e62
             grind)
          | exact superpose b0e62 b0e63
          | exact resolve b0e63 b0e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e62 b0e63
        have b0e66 : False := by grind
        exact b0e66
      · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b1e21 : (M.op x y) = (M.op x x) := by grind
          have b1e23 : (M.op y y) ≠ (M.op y x) := by grind
          have b1e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e26 : x ≠ (M.op y x) := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e23
            | exact resolve b1e23 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e31 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b1e13 X0 y y
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e36 : y = (M.op y (M.op y (M.op x x))) := by
            first
            | (have i₁ := b1e31 y
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e31
            | exact resolve b1e31 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e41 : x = y := by
            first
            | (have i₁ := b1e36
               have i₂ := b1e31 x
               grind)
            | exact superpose b1e31 b1e36
            | exact resolve b1e36 b1e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e31 b1e36
          have b1e45 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b1e26
               have i₂ := b1e41
               grind)
            | exact superpose b1e41 b1e26
            | exact resolve b1e26 b1e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e26
          have b1e46 : x = (M.op x x) := by
            first
            | (have i₁ := b1e24
               have i₂ := b1e41
               grind)
            | exact superpose b1e41 b1e24
            | exact resolve b1e24 b1e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e41
          have b1e47 : False := by grind
          exact b1e47
        · have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : (M.op x y) = (M.op x x) := by grind
          have b2e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e20
            | exact resolve b2e20 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e27 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b2e26
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e26
            | exact resolve b2e26 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e26
          have b2e47 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have i₁ := b2e16 x y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e16
            | (have j0 := b2e16 x x
               grind)
            | (have r₁ := b2e16 x y
               have r₂ := b2e21
               grind)
            | exact resolve b2e16 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e49 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b2e16 (σ x) (σ y)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e16
            | (have j0 := b2e16 (σ x) (σ x)
               grind)
            | (have r₁ := b2e16 (σ x) (σ y)
               have r₂ := b2e22
               grind)
            | exact resolve b2e16 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e51 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b2e49
          have b2e52 : (M.op x x) = (k x y) := by grind
          clear b2e47
          have b2e53 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b2e51
               have i₂ := b2e19 x y
               grind)
            | exact superpose b2e19 b2e51
            | exact resolve b2e51 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e51
          have b2e54 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b2e53
               have i₂ := b2e52
               grind)
            | exact superpose b2e52 b2e53
            | exact resolve b2e53 b2e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e52 b2e53
          have b2e55 : False := by grind
          exact b2e55
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
        · have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : (M.op x y) = (M.op x x) := by grind
          have b3e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b3e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e22
            | exact resolve b3e22 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e27 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e20
            | exact resolve b3e20 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e50 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have i₁ := b3e16 x y
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e16
            | (have j0 := b3e16 x x
               grind)
            | (have r₁ := b3e16 x y
               have r₂ := b3e21
               grind)
            | exact resolve b3e16 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e52 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b3e16 (σ x) (σ x)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e16
            | exact resolve b3e16 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b3e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e55 : (σ y) = (k (σ x) (σ x)) := by grind
          clear b3e52
          have b3e57 : (M.op x x) = (k x y) := by grind
          clear b3e50
          have b3e58 : (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b3e55
               have i₂ := b3e19 x x
               grind)
            | exact superpose b3e19 b3e55
            | exact resolve b3e55 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e55
          have b3e60 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b3e58
               have i₂ := b3e54 x
               grind)
            | exact superpose b3e54 b3e58
            | exact resolve b3e58 b3e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e58
          have b3e62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b3e19 X0 X0
               have i₂ := b3e54 (σ X0)
               grind)
            | exact superpose b3e54 b3e19
            | exact resolve b3e19 b3e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b3e62 X0
               have i₂ := b3e54 X0
               grind)
            | exact superpose b3e54 b3e62
            | exact resolve b3e62 b3e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e54 b3e62
          have b3e72 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          have b3e75 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e72
               have r₂ := b3e26
               grind)
            | exact resolve b3e72 b3e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26 b3e72
          have b3e77 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b3e75
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e75
            | exact resolve b3e75 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e75
          have b3e78 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b3e77
               have i₂ := b3e57
               grind)
            | exact superpose b3e57 b3e77
            | exact resolve b3e77 b3e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e57 b3e77
          have b3e114 : (σ x) = (σ y) := by
            first
            | (have i₁ := b3e60
               have i₂ := b3e78
               grind)
            | exact superpose b3e78 b3e60
            | exact resolve b3e60 b3e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e60 b3e78
          have b3e151 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b3e27
               have i₂ := b3e114
               grind)
            | exact superpose b3e114 b3e27
            | exact resolve b3e27 b3e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e27 b3e114
          have b3e160 : False := by grind
          exact b3e160
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b4e22 : (M.op x y) = (M.op x x) := by grind
            have b4e25 : (M.op y y) ≠ (M.op y x) := by grind
            have b4e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : x ≠ (M.op y x) := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e25
              | exact resolve b4e25 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e33 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b4e14 X0 y y
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e14
              | exact resolve b4e14 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e39 : y = (M.op y (M.op y (M.op x x))) := by
              first
              | (have i₁ := b4e33 y
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e33
              | exact resolve b4e33 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e44 : x = y := by
              first
              | (have i₁ := b4e39
                 have i₂ := b4e33 x
                 grind)
              | exact superpose b4e33 b4e39
              | exact resolve b4e39 b4e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e33 b4e39
            have b4e67 : x = (M.op x x) := by
              first
              | (have i₁ := b4e26
                 have i₂ := b4e44
                 grind)
              | exact superpose b4e44 b4e26
              | exact resolve b4e26 b4e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e68 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b4e28
                 have i₂ := b4e44
                 grind)
              | exact superpose b4e44 b4e28
              | exact resolve b4e28 b4e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e28 b4e44
            have b4e74 : False := by grind
            exact b4e74
          · have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b5e22 : (M.op x y) = (M.op x x) := by grind
            have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
            have b5e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e23
              | exact resolve b5e23 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e29 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b5e21
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e21
              | exact resolve b5e21 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e42 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
              first
              | (have i₁ := b5e17 x y
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e17
              | (have j0 := b5e17 x x
                 grind)
              | (have r₁ := b5e17 x y
                 have r₂ := b5e22
                 grind)
              | exact resolve b5e17 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e43 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b5e17 (σ x) (σ x)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e17
              | exact resolve b5e17 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b5e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e46 : (σ y) = (k (σ x) (σ x)) := by grind
            clear b5e43
            have b5e47 : (M.op x x) = (k x y) := by grind
            clear b5e42
            have b5e48 : (σ y) = (σ (k x x)) := by
              first
              | (have i₁ := b5e46
                 have i₂ := b5e20 x x
                 grind)
              | exact superpose b5e20 b5e46
              | exact resolve b5e46 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e46
            have b5e49 : (σ y) = (σ (M.op x x)) := by
              first
              | (have i₁ := b5e48
                 have i₂ := b5e45 x
                 grind)
              | exact superpose b5e45 b5e48
              | exact resolve b5e48 b5e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e48
            have b5e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b5e20 X0 X0
                 have i₂ := b5e45 (σ X0)
                 grind)
              | exact superpose b5e45 b5e20
              | exact resolve b5e20 b5e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b5e51 X0
                 have i₂ := b5e45 X0
                 grind)
              | exact superpose b5e45 b5e51
              | exact resolve b5e51 b5e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e45 b5e51
            have b5e57 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
            have b5e60 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e57
                 have r₂ := b5e28
                 grind)
              | exact resolve b5e57 b5e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e28 b5e57
            have b5e62 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b5e60
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e60
              | exact resolve b5e60 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e60
            have b5e63 : (σ x) = (σ (M.op x x)) := by
              first
              | (have i₁ := b5e62
                 have i₂ := b5e47
                 grind)
              | exact superpose b5e47 b5e62
              | exact resolve b5e62 b5e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e47 b5e62
            have b5e98 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e49
                 have i₂ := b5e63
                 grind)
              | exact superpose b5e63 b5e49
              | exact resolve b5e49 b5e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e49 b5e63
            have b5e127 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b5e29
                 have i₂ := b5e98
                 grind)
              | exact superpose b5e98 b5e29
              | exact resolve b5e29 b5e98
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e29 b5e98
            have b5e136 : False := by grind
            exact b5e136
      · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b6e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : (M.op y y) = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) (M.op X2 (M.op X0 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e13 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
               have i₂ := b6e13 X0 X2 X1
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e305 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op (M.op X0 X1) y)) (M.op X1 (M.op y x))) := by
            intro X0 X1
            first
            | (have i₁ := b6e31 y X0 X1 y
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e31
            | exact resolve b6e31 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e341 : x = y := by
            first
            | (have i₁ := b6e305 x x
               have i₂ := b6e31 y x x x
               grind)
            | exact superpose b6e31 b6e305
            | exact resolve b6e305 b6e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e31 b6e305
          have b6e391 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e341
               grind)
            | exact superpose b6e341 b6e22
            | exact resolve b6e22 b6e341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e341
          have b6e398 : False := by grind
          exact b6e398
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b7e22 : (M.op x y) = (M.op x x) := by grind
            have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
            have b7e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e36 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b7e14 X0 y y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e41 : y = (M.op y (M.op y (M.op x x))) := by
              first
              | (have i₁ := b7e36 y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e36
              | exact resolve b7e36 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e46 : x = y := by
              first
              | (have i₁ := b7e41
                 have i₂ := b7e36 x
                 grind)
              | exact superpose b7e36 b7e41
              | exact resolve b7e41 b7e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e36 b7e41
            have b7e47 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e23
                 have i₂ := b7e46
                 grind)
              | exact superpose b7e46 b7e23
              | exact resolve b7e23 b7e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e46
            have b7e52 : False := by grind
            exact b7e52
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b8e22 : (M.op x y) = (M.op x x) := by grind
            have b8e25 : (M.op y y) ≠ (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e35 : ∀ X0 : G, (M.op y (M.op x (M.op (M.op x x) X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b8e14 X0 y x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e38 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X1) X2) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 (M.op (M.op (M.op X2 X1) X2) X0) X1 X2
                 have i₂ := b8e14 X0 X2 (M.op X2 X1)
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e131 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x x) x) X0) := by
              intro X0
              first
              | (have i₁ := b8e35 (M.op (M.op (M.op x x) x) X0)
                 have i₂ := b8e14 X0 x (M.op x x)
                 grind)
              | exact superpose b8e14 b8e35
              | exact resolve b8e35 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e35
            have b8e134 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b8e131 X0
                 have i₂ := b8e38 X0 x x
                 grind)
              | exact superpose b8e38 b8e131
              | exact resolve b8e131 b8e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e38 b8e131
            have b8e147 : (M.op x y) ≠ (M.op y x) := by
              first
              | (have i₁ := b8e25
                 have i₂ := b8e134 y
                 grind)
              | exact superpose b8e134 b8e25
              | exact resolve b8e25 b8e134
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e150 : (M.op x y) ≠ (M.op x x) := by
              first
              | (have i₁ := b8e147
                 have i₂ := b8e134 x
                 grind)
              | exact superpose b8e134 b8e147
              | exact resolve b8e147 b8e134
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e134 b8e147
            have b8e156 : False := by grind
            exact b8e156
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b9e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b9e22 : y = (M.op x x) := by grind
          have b9e24 : (M.op y y) = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e26 : y ≠ (M.op x y) := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e21
            | exact resolve b9e21 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e30 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b9e13 X0 x x
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e13
            | exact resolve b9e13 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e35 : y = (M.op x (M.op x (M.op y x))) := by
            first
            | (have i₁ := b9e30 y
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e30
            | exact resolve b9e30 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e39 : x = y := by
            first
            | (have i₁ := b9e35
               have i₂ := b9e30 x
               grind)
            | exact superpose b9e30 b9e35
            | exact resolve b9e35 b9e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e30 b9e35
          have b9e43 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b9e26
               have i₂ := b9e39
               grind)
            | exact superpose b9e39 b9e26
            | exact resolve b9e26 b9e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26
          have b9e44 : x ≠ y := by
            first
            | (have i₁ := b9e43
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e43
            | exact resolve b9e43 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e43
          have b9e45 : False := by grind
          exact b9e45
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b10e22 : (M.op x y) ≠ (M.op x x) := by grind
            have b10e23 : y = (M.op x x) := by grind
            have b10e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e29 : y ≠ (M.op x y) := by
              first
              | (have i₁ := b10e22
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e22
              | exact resolve b10e22 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e37 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b10e14 X0 x x
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e14
              | exact resolve b10e14 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e42 : y = (M.op x (M.op x x)) := by
              first
              | (have i₁ := b10e37 y
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e37
              | exact resolve b10e37 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e37
            have b10e46 : y = (M.op x y) := by
              first
              | (have i₁ := b10e42
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e42
              | exact resolve b10e42 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e42
            have b10e47 : False := by grind
            exact b10e47
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : (M.op x y) ≠ (M.op x x) := by grind
            have b11e23 : y = (M.op x x) := by grind
            have b11e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            have b11e25 : (M.op y y) ≠ (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e28 : y ≠ (M.op x y) := by
              first
              | (have i₁ := b11e22
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e22
              | exact resolve b11e22 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e57 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 (σ x) (σ x)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b11e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e62 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
            clear b11e57
            have b11e65 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b11e62
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e62
              | exact resolve b11e62 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e62
            have b11e78 : x = (k x y) ∨ y = (M.op x y) := by grind
            have b11e81 : x = (k x y) := by
              first
              | (have r₁ := b11e78
                 have r₂ := b11e28
                 grind)
              | exact resolve b11e78 b11e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e28 b11e78
            have b11e189 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ x)
                 have i₂ := b11e65
                 grind)
              | exact superpose b11e65 b11e17
              | exact resolve b11e17 b11e65
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e65
            have b11e194 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
            clear b11e189
            have b11e199 : (σ (k x y)) = (σ (k x x)) := by
              first
              | (have i₁ := b11e194
                 have i₂ := b11e20 x x
                 grind)
              | exact superpose b11e20 b11e194
              | exact resolve b11e194 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e194
            have b11e205 : (σ (k x y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b11e199
                 have i₂ := b11e60 x
                 grind)
              | exact superpose b11e60 b11e199
              | exact resolve b11e199 b11e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e60 b11e199
            have b11e208 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b11e205
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e205
              | exact resolve b11e205 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e205
            have b11e211 : (σ x) = (σ y) := by
              first
              | (have i₁ := b11e208
                 have i₂ := b11e81
                 grind)
              | exact superpose b11e81 b11e208
              | exact resolve b11e208 b11e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e81 b11e208
            have b11e215 : y = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 y
                 have i₂ := b11e211
                 grind)
              | exact superpose b11e211 b11e15
              | exact resolve b11e15 b11e211
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e211
            have b11e216 : x = y := by
              first
              | (have i₁ := b11e215
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e215
              | exact resolve b11e215 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e215
            have b11e277 : (M.op x x) ≠ (M.op x x) := by
              first
              | (have i₁ := b11e25
                 have i₂ := b11e216
                 grind)
              | exact superpose b11e216 b11e25
              | exact resolve b11e25 b11e216
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e216
            have b11e286 : False := by grind
            exact b11e286
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b12e22 : (M.op x y) ≠ (M.op x x) := by grind
            have b12e23 : y = (M.op x x) := by grind
            have b12e26 : (M.op y y) = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e29 : y ≠ (M.op x y) := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e22
              | exact resolve b12e22 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e34 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b12e14 X0 x x
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e14
              | exact resolve b12e14 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e38 : y = (M.op x (M.op x (M.op y x))) := by
              first
              | (have i₁ := b12e34 y
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e34
              | exact resolve b12e34 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e42 : x = y := by
              first
              | (have i₁ := b12e38
                 have i₂ := b12e34 x
                 grind)
              | exact superpose b12e34 b12e38
              | exact resolve b12e38 b12e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e34 b12e38
            have b12e77 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b12e29
                 have i₂ := b12e42
                 grind)
              | exact superpose b12e42 b12e29
              | exact resolve b12e29 b12e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e29
            have b12e78 : x ≠ y := by
              first
              | (have i₁ := b12e77
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e77
              | exact resolve b12e77 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e77
            have b12e81 : False := by grind
            exact b12e81
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b13e23 : (M.op x y) ≠ (M.op x x) := by grind
              have b13e24 : y = (M.op x x) := by grind
              have b13e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e32 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b13e23
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e23
                | exact resolve b13e23 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e41 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b13e15 X0 x x
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e45 : y = (M.op x (M.op x x)) := by
                first
                | (have i₁ := b13e41 y
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e41
                | exact resolve b13e41 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e41
              have b13e49 : y = (M.op x y) := by
                first
                | (have i₁ := b13e45
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e45
                | exact resolve b13e45 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e45
              have b13e50 : False := by grind
              exact b13e50
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : y = (M.op x x) := by grind
              have b14e25 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
              have b14e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e30 : (σ y) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e25
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e25
                | exact resolve b14e25 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 (τ X0) X1
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e21
                | exact resolve b14e21 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X1 (τ X0)
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e21
                | exact resolve b14e21 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e38 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e15 X0 x x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e39 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e15 X0 (σ x) (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e15
                | exact resolve b14e15 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) (M.op X2 (M.op X0 X3))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
                   have i₂ := b14e15 X0 X2 X1
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e41 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X2 X0)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 (M.op X3 (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
                   have i₂ := b14e15 X0 (M.op X2 X1) X3
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e42 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X1) X2) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 (M.op (M.op (M.op X2 X1) X2) X0) X1 X2
                   have i₂ := b14e15 X0 X2 (M.op X2 X1)
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e44 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y x) X0) := by
                intro X0
                first
                | (have i₁ := b14e38 (M.op (M.op y x) X0)
                   have i₂ := b14e15 X0 x y
                   grind)
                | exact superpose b14e15 b14e38
                | exact resolve b14e38 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b14e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b14e21 X0 X0
                   have i₂ := b14e52 (σ X0)
                   grind)
                | exact superpose b14e52 b14e21
                | exact resolve b14e21 b14e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e62 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b14e32 X0 (τ X0)
                   have i₂ := b14e52 (τ X0)
                   grind)
                | exact superpose b14e52 b14e32
                | exact resolve b14e32 b14e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e32
              have b14e63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b14e62 X0
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e62
                | exact resolve b14e62 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e62
              have b14e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b14e61 X0
                   have i₂ := b14e52 X0
                   grind)
                | exact superpose b14e52 b14e61
                | exact resolve b14e61 b14e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e61
              have b14e66 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b14e63 X0
                   have i₂ := b14e52 X0
                   grind)
                | exact superpose b14e52 b14e63
                | exact resolve b14e63 b14e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e52 b14e63
              have b14e88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e18 X0 X1
                   have i₂ := b14e20 X0 X1
                   grind)
                | (have i₁ := b14e18 X0 X0
                   have i₂ := b14e20 X0 X1
                   grind)
                | exact superpose b14e20 b14e18
                | (have j0 := b14e18 X0 X0
                   have j1 := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e18 X0 X1
                   have r₂ := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e18 X1 X1
                   have r₂ := b14e20 X1 X1
                   grind)
                | (have r₁ := b14e18 X0 X1
                   have r₂ := b14e20 X0 (M.op X0 X1)
                   grind)
                | exact resolve b14e18 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e88 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e88
              have b14e105 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e15 X0 x y
                   have i₂ := b14e44 X0
                   grind)
                | exact superpose b14e44 b14e15
                | exact resolve b14e15 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e44
              have b14e137 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e16 (k X0 (τ X1))
                   have i₂ := b14e33 X1 X0
                   grind)
                | exact superpose b14e33 b14e16
                | exact resolve b14e16 b14e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e33
              have b14e142 : x = (M.op x (M.op y y)) := by
                first
                | (have i₁ := b14e105 x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e105
                | exact resolve b14e105 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e143 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x X0)) := by
                intro X0
                first
                | (have i₁ := b14e105 (M.op y (M.op x X0))
                   have i₂ := b14e105 X0
                   grind)
                | exact superpose b14e105 b14e105
                | exact resolve b14e105 b14e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e166 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X3) = (M.op (M.op X0 X2) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e42 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
                   have i₂ := b14e15 X0 X2 X1
                   grind)
                | exact superpose b14e15 b14e42
                | exact resolve b14e42 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e168 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X0) X0) X2) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e42 X2 X1 X0
                   have i₂ := b14e20 X0 X1
                   grind)
                | (have i₁ := b14e42 X0 X0 X0
                   have i₂ := b14e20 X0 X1
                   grind)
                | exact superpose b14e20 b14e42
                | (have j1 := b14e20 X0 X1
                   grind)
                | exact resolve b14e42 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e175 : ∀ X0 : G, (M.op (M.op x x) X0) = (M.op (M.op y y) X0) := by
                intro X0
                first
                | (have i₁ := b14e42 X0 (M.op y y) x
                   have i₂ := b14e142
                   grind)
                | exact superpose b14e142 b14e42
                | exact resolve b14e42 b14e142
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e142
              have b14e177 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e42 X2 X1 (M.op X1 X0)
                   have i₂ := b14e42 (M.op X1 X0) X0 X1
                   grind)
                | exact superpose b14e42 b14e42
                | exact resolve b14e42 b14e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e181 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) (M.op X0 X1))) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X1 X2 (M.op X2 X0)
                   have i₂ := b14e42 X1 X0 X2
                   grind)
                | exact superpose b14e42 b14e15
                | exact resolve b14e15 b14e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e201 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
                intro X0
                first
                | (have i₁ := b14e175 X0
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e175
                | exact resolve b14e175 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e175
              have b14e203 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e168 X0 X1 X2
                   have i₂ := b14e42 X2 X0 X0
                   grind)
                | exact superpose b14e42 b14e168
                | (have j0 := b14e168 X0 X1 X2
                   grind)
                | exact resolve b14e168 b14e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e168
              have b14e277 : ∀ X0 : G, (M.op y (M.op y (M.op y X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e15 X0 y y
                   have i₂ := b14e201 X0
                   grind)
                | exact superpose b14e201 b14e15
                | exact resolve b14e15 b14e201
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e340 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op (M.op X0 X1) (σ x))) (M.op X1 (σ y))) := by
                intro X0 X1
                first
                | (have i₁ := b14e40 (σ x) X0 X1 (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e40
                | exact resolve b14e40 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e341 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (M.op X1 X2) (σ x))) (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e40 (σ x) X1 X2 (M.op (σ x) (M.op (σ y) X0))
                   have i₂ := b14e39 X0
                   grind)
                | exact superpose b14e39 b14e40
                | exact resolve b14e40 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e397 : ∀ X0 X2 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op (σ x) X2) (M.op X2 X0)) := by
                intro X0 X2
                first
                | (have i₁ := b14e341 X0 x X2
                   have i₂ := b14e166 (σ x) x X2 (M.op X2 X0)
                   grind)
                | exact superpose b14e166 b14e341
                | exact resolve b14e341 b14e166
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e341
              have b14e398 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) X1) (M.op X1 (σ y))) := by
                intro X1
                first
                | (have i₁ := b14e340 x X1
                   have i₂ := b14e166 (σ x) x X1 (M.op X1 (σ y))
                   grind)
                | exact superpose b14e166 b14e340
                | exact resolve b14e340 b14e166
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e340
              have b14e441 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
                first
                | (have i₁ := b14e398 x
                   have i₂ := b14e397 (σ y) x
                   grind)
                | exact superpose b14e397 b14e398
                | exact resolve b14e398 b14e397
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e398
              have b14e453 : (σ x) = (M.op (σ x) (σ (M.op y y))) := by
                first
                | (have i₁ := b14e441
                   have i₂ := b14e64 y
                   grind)
                | exact superpose b14e64 b14e441
                | exact resolve b14e441 b14e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e441
              have b14e457 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op y X0)) := by
                intro X0
                first
                | (have i₁ := b14e38 (M.op y (M.op y X0))
                   have i₂ := b14e277 X0
                   grind)
                | exact superpose b14e277 b14e38
                | exact resolve b14e38 b14e277
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e38 b14e277
              have b14e490 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X3)) (M.op X0 X4)) = (M.op (M.op X3 X0) (M.op X2 X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b14e41 X4 (M.op X3 X0) X2 (M.op X1 (M.op (M.op X1 X2) X3))
                   have i₂ := b14e40 X3 X1 X2 X0
                   grind)
                | exact superpose b14e40 b14e41
                | exact resolve b14e41 b14e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e556 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op X0 X4)) = (M.op (M.op X3 X0) (M.op X2 X4)) := by
                intro X0 X2 X3 X4
                first
                | (have i₁ := b14e490 X0 x X2 X3 X4
                   have i₂ := b14e166 X3 x X2 (M.op X0 X4)
                   grind)
                | exact superpose b14e166 b14e490
                | exact resolve b14e490 b14e166
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e490
              have b14e642 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (M.op X1 (M.op (M.op X1 (σ (M.op X0 X0))) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e41 X2 (σ X0) (σ X0) X1
                   have i₂ := b14e64 X0
                   grind)
                | exact superpose b14e64 b14e41
                | exact resolve b14e41 b14e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e692 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b14e16 (M.op (τ X0) (τ X0))
                   have i₂ := b14e66 X0
                   grind)
                | exact superpose b14e66 b14e16
                | exact resolve b14e16 b14e66
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e749 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e92 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e92
              have b14e752 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e749 X0 X1
                   have j1 := b14e203 X0 X1 x
                   grind)
                | (have r₁ := b14e749 x X0
                   have r₂ := b14e203 X0 x x
                   grind)
                | (have r₁ := b14e749 x X1
                   have r₂ := b14e203 x X1 x
                   grind)
                | (have r₁ := b14e749 X0 X1
                   have r₂ := b14e203 X0 (M.op X1 X0) x
                   grind)
                | exact resolve b14e749 b14e203
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e203 b14e749
              have b14e830 : ∀ X0 X1 : G, (σ (M.op y y)) = (M.op (M.op X0 (M.op (M.op X0 X1) (σ x))) (M.op X1 (σ x))) := by
                intro X0 X1
                first
                | (have i₁ := b14e40 (σ x) X0 X1 (σ (M.op y y))
                   have i₂ := b14e453
                   grind)
                | exact superpose b14e453 b14e40
                | exact resolve b14e40 b14e453
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e832 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (σ (M.op y y)) X0) := by
                intro X0
                first
                | (have i₁ := b14e42 X0 (σ (M.op y y)) (σ x)
                   have i₂ := b14e453
                   grind)
                | exact superpose b14e453 b14e42
                | exact resolve b14e42 b14e453
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e42 b14e453
              have b14e834 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y y)) X0) := by
                intro X0
                first
                | (have i₁ := b14e832 X0
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e832
                | exact resolve b14e832 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e832
              have b14e835 : ∀ X1 : G, (σ (M.op y y)) = (M.op (M.op (σ x) X1) (M.op X1 (σ x))) := by
                intro X1
                first
                | (have i₁ := b14e830 x X1
                   have i₂ := b14e166 (σ x) x X1 (M.op X1 (σ x))
                   grind)
                | exact superpose b14e166 b14e830
                | exact resolve b14e830 b14e166
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e830
              have b14e838 : (σ (M.op y y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
                first
                | (have i₁ := b14e835 x
                   have i₂ := b14e397 (σ x) x
                   grind)
                | exact superpose b14e397 b14e835
                | exact resolve b14e835 b14e397
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e835
              have b14e1039 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op X1 (M.op (M.op X1 X2) (τ X0))) (M.op X2 (τ (M.op X0 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e40 (τ X0) X1 X2 (τ X0)
                   have i₂ := b14e692 X0
                   grind)
                | exact superpose b14e692 b14e40
                | exact resolve b14e40 b14e692
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e40 b14e692
              have b14e1053 : ∀ X0 X2 : G, (τ X0) = (M.op (M.op (τ X0) X2) (M.op X2 (τ (M.op X0 X0)))) := by
                intro X0 X2
                first
                | (have i₁ := b14e1039 X0 x X2
                   have i₂ := b14e166 (τ X0) x X2 (M.op X2 (τ (M.op X0 X0)))
                   grind)
                | exact superpose b14e166 b14e1039
                | exact resolve b14e1039 b14e166
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e166 b14e1039
              have b14e1242 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
                intro X0
                first
                | (have i₁ := b14e177 (σ x) (σ x) X0
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e177
                | exact resolve b14e177 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e177
              have b14e1530 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e181 (σ x) X0 (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e181
                | exact resolve b14e181 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e181
              have b14e2300 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b14e64 (M.op y y)
                   have i₂ := b14e834 (σ (M.op y y))
                   grind)
                | exact superpose b14e834 b14e64
                | exact resolve b14e64 b14e834
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e2330 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (M.op (M.op X0 (σ (M.op y y))) X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X1 (σ (M.op y y)) X0
                   have i₂ := b14e834 (M.op X0 (M.op (M.op X0 (σ (M.op y y))) X1))
                   grind)
                | exact superpose b14e834 b14e15
                | exact resolve b14e15 b14e834
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e834
              have b14e2354 : ∀ X1 : G, (M.op (σ y) (M.op (σ y) (M.op (σ y) X1))) = X1 := by
                intro X1
                first
                | (have i₁ := b14e2330 x X1
                   have i₂ := b14e642 y x X1
                   grind)
                | exact superpose b14e642 b14e2330
                | exact resolve b14e2330 b14e642
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e642 b14e2330
              have b14e2370 : (σ (M.op y (M.op y y))) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b14e2300
                   have i₂ := b14e201 (M.op y y)
                   grind)
                | exact superpose b14e201 b14e2300
                | exact resolve b14e2300 b14e201
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e201 b14e2300
              have b14e2387 : (σ (M.op x (M.op x y))) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b14e2370
                   have i₂ := b14e457 y
                   grind)
                | exact superpose b14e457 b14e2370
                | exact resolve b14e2370 b14e457
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e457 b14e2370
              have b14e2808 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ y) = X0 := by
                intro X0
                first
                | (have i₁ := b14e26
                   have i₂ := b14e752 (σ x) X0
                   grind)
                | (have i₁ := b14e26
                   have i₂ := b14e752 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b14e752 b14e26
                | (have j1 := b14e752 (σ x) X0
                   grind)
                | exact resolve b14e26 b14e752
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e2816 : ∀ X0 X1 : G, (σ X0) = (M.op X1 X1) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e66 X1
                   have i₂ := b14e752 (τ X1) X0
                   grind)
                | (have i₁ := b14e66 X0
                   have i₂ := b14e752 X0 (M.op (τ X0) (τ X0))
                   grind)
                | exact superpose b14e752 b14e66
                | (have j1 := b14e752 (τ X1) X0
                   grind)
                | exact resolve b14e66 b14e752
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e66 b14e752
              have b14e5719 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) X0) (M.op (σ y) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e41 X1 (M.op (σ x) X0) (σ y) (σ x)
                   have i₂ := b14e1530 X0
                   grind)
                | exact superpose b14e1530 b14e41
                | exact resolve b14e41 b14e1530
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e41 b14e1530
              have b14e6965 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
                intro X0
                first
                | (have i₁ := b14e39 (M.op (σ y) (M.op (σ y) X0))
                   have i₂ := b14e2354 X0
                   grind)
                | exact superpose b14e2354 b14e39
                | exact resolve b14e39 b14e2354
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e39 b14e2354
              have b14e13419 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 (σ x))) ∨ (σ y) = X0 := by
                intro X0
                first
                | (have i₁ := b14e137 x X0
                   have i₂ := b14e2808 X0
                   grind)
                | exact superpose b14e2808 b14e137
                | (have j1 := b14e2808 X0
                   grind)
                | exact resolve b14e137 b14e2808
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e137 b14e2808
              have b14e21745 : (M.op (σ x) (M.op (σ y) (M.op (σ y) (σ x)))) = (M.op (M.op (σ x) (σ x)) (σ (M.op y y))) := by
                first
                | (have i₁ := b14e397 (M.op (σ y) (σ x)) (σ x)
                   have i₂ := b14e838
                   grind)
                | exact superpose b14e838 b14e397
                | exact resolve b14e397 b14e838
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e397 b14e838
              have b14e21980 : (M.op (σ y) (σ (M.op y y))) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (σ x)))) := by
                first
                | (have i₁ := b14e21745
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e21745
                | exact resolve b14e21745 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e21745
              have b14e22111 : (M.op (σ y) (σ (M.op y y))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) := by
                first
                | (have i₁ := b14e21980
                   have i₂ := b14e6965 (σ x)
                   grind)
                | exact superpose b14e6965 b14e21980
                | exact resolve b14e21980 b14e6965
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6965 b14e21980
              have b14e22192 : (M.op (σ y) (σ (M.op y y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
                first
                | (have i₁ := b14e22111
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e22111
                | exact resolve b14e22111 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e22111
              have b14e22242 : (σ (M.op x (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
                first
                | (have i₁ := b14e22192
                   have i₂ := b14e2387
                   grind)
                | exact superpose b14e2387 b14e22192
                | exact resolve b14e22192 b14e2387
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e2387 b14e22192
              have b14e222310 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e13419 (M.op (σ x) (σ y))
                   have i₂ := b14e1242 (σ x)
                   grind)
                | exact superpose b14e1242 b14e13419
                | (have j0 := b14e13419 (M.op (σ x) (σ y))
                   grind)
                | exact resolve b14e13419 b14e1242
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1242 b14e13419
              have b14e222428 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ y)))) := by
                first
                | (have r₁ := b14e222310
                   have r₂ := b14e30
                   grind)
                | exact resolve b14e222310 b14e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e222310
              have b14e222455 : (τ (σ y)) = (k x (τ (M.op (σ x) (σ y)))) := by
                first
                | (have i₁ := b14e222428
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e222428
                | exact resolve b14e222428 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e222428
              have b14e222467 : y = (k x (τ (M.op (σ x) (σ y)))) := by
                first
                | (have i₁ := b14e222455
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e222455
                | exact resolve b14e222455 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e222455
              have b14e343503 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (τ (σ X1))) = (k (τ (σ X1)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e64 X1
                   have i₂ := b14e2816 X0 (σ X1)
                   grind)
                | exact superpose b14e2816 b14e64
                | (have j1 := b14e2816 X0 (σ X1)
                   grind)
                | exact resolve b14e64 b14e2816
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e64 b14e2816
              have b14e343535 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X0) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e343503 X0 X0
                   have i₂ := b14e16 X0
                   grind)
                | exact superpose b14e16 b14e343503
                | (have j0 := b14e343503 X0 X1
                   grind)
                | exact resolve b14e343503 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e343503
              have b14e356204 : y = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (σ (M.op x x)) = (σ (τ (M.op (σ x) (σ y)))) := by
                first
                | (have i₁ := b14e222467
                   have i₂ := b14e343535 (τ (M.op (σ x) (σ y))) x
                   grind)
                | exact superpose b14e343535 b14e222467
                | (have j1 := b14e343535 (τ (M.op (σ x) (σ y))) x
                   grind)
                | exact resolve b14e222467 b14e343535
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e222467 b14e343535
              have b14e356316 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op (τ (M.op (σ x) (σ y))) x) := by
                first
                | (have i₁ := b14e356204
                   have i₂ := b14e17 (M.op (σ x) (σ y))
                   grind)
                | exact superpose b14e17 b14e356204
                | exact resolve b14e356204 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e356204
              have b14e356348 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op (τ (M.op (σ x) (σ y))) x) := by
                first
                | (have i₁ := b14e356316
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e356316
                | exact resolve b14e356316 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e356316
              have b14e356354 : y = (M.op (τ (M.op (σ x) (σ y))) x) := by
                first
                | (have r₁ := b14e356348
                   have r₂ := b14e30
                   grind)
                | exact resolve b14e356348 b14e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e30 b14e356348
              have b14e358072 : (τ (M.op (σ x) (σ y))) = (M.op y (M.op x (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
                first
                | (have i₁ := b14e1053 (M.op (σ x) (σ y)) x
                   have i₂ := b14e356354
                   grind)
                | exact superpose b14e356354 b14e1053
                | exact resolve b14e1053 b14e356354
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1053 b14e356354
              have b14e358248 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op y (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
                first
                | (have i₁ := b14e358072
                   have i₂ := b14e143 (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))
                   grind)
                | exact superpose b14e143 b14e358072
                | exact resolve b14e358072 b14e143
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e143 b14e358072
              have b14e358293 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op y (τ (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y)))))) := by
                first
                | (have i₁ := b14e358248
                   have i₂ := b14e556 (σ x) (σ y) (σ x) (σ y)
                   grind)
                | (have i₁ := b14e358248
                   have i₂ := b14e556 (σ y) (σ x) (σ x) (σ y)
                   grind)
                | exact superpose b14e556 b14e358248
                | exact resolve b14e358248 b14e556
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e556 b14e358248
              have b14e358317 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op y (τ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
                first
                | (have i₁ := b14e358293
                   have i₂ := b14e5719 (σ x) (σ y)
                   grind)
                | exact superpose b14e5719 b14e358293
                | exact resolve b14e358293 b14e5719
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e5719 b14e358293
              have b14e358337 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op y (τ (σ (M.op x (M.op x y)))))) := by
                first
                | (have i₁ := b14e358317
                   have i₂ := b14e22242
                   grind)
                | exact superpose b14e22242 b14e358317
                | exact resolve b14e358317 b14e22242
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e22242 b14e358317
              have b14e358347 : (M.op x (M.op y (M.op x (M.op x y)))) = (τ (M.op (σ x) (σ y))) := by
                first
                | (have i₁ := b14e358337
                   have i₂ := b14e16 (M.op x (M.op x y))
                   grind)
                | exact superpose b14e16 b14e358337
                | exact resolve b14e358337 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e358337
              have b14e358354 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
                first
                | (have i₁ := b14e358347
                   have i₂ := b14e105 (M.op x y)
                   grind)
                | exact superpose b14e105 b14e358347
                | exact resolve b14e358347 b14e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e105 b14e358347
              have b14e359304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e17 (M.op (σ x) (σ y))
                   have i₂ := b14e358354
                   grind)
                | exact superpose b14e358354 b14e17
                | exact resolve b14e17 b14e358354
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e358354
              have b14e359319 : False := by grind
              exact b14e359319
        · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b15e23 : y = (M.op x x) := by grind
            have b15e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e26 : (M.op y y) = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e35 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b15e14 X0 x x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e40 : y = (M.op x (M.op x (M.op y x))) := by
              first
              | (have i₁ := b15e35 y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e35
              | exact resolve b15e35 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e44 : x = y := by
              first
              | (have i₁ := b15e40
                 have i₂ := b15e35 x
                 grind)
              | exact superpose b15e35 b15e40
              | exact resolve b15e40 b15e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e35 b15e40
            have b15e45 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e24
                 have i₂ := b15e44
                 grind)
              | exact superpose b15e44 b15e24
              | exact resolve b15e24 b15e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e44
            have b15e49 : False := by grind
            exact b15e49
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b16e23 : (M.op x y) ≠ (M.op x x) := by grind
              have b16e24 : y = (M.op x x) := by grind
              have b16e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e31 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b16e23
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e23
                | exact resolve b16e23 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e34 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b16e15 X0 x x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e39 : y = (M.op x (M.op x x)) := by
                first
                | (have i₁ := b16e34 y
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e34
                | exact resolve b16e34 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e34
              have b16e43 : y = (M.op x y) := by
                first
                | (have i₁ := b16e39
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e39
                | exact resolve b16e39 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e39
              have b16e44 : False := by grind
              exact b16e44
            · have b17e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e24 : y = (M.op x x) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b17e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b17e21 X0 X0
                   have i₂ := b17e55 (σ X0)
                   grind)
                | exact superpose b17e55 b17e21
                | exact resolve b17e21 b17e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b17e64 X0
                   have i₂ := b17e55 X0
                   grind)
                | exact superpose b17e55 b17e64
                | exact resolve b17e64 b17e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e55 b17e64
              have b17e527 : (σ y) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e65 x
                   grind)
                | exact superpose b17e65 b17e26
                | exact resolve b17e26 b17e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e65
              have b17e542 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b17e527
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e527
                | exact resolve b17e527 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e527
              have b17e543 : False := by grind
              exact b17e543
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b18e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b18e24 : (M.op y y) = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e29 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op y x) X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b18e13 X0 y y
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e32 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X1) X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 (M.op (M.op (M.op X2 X1) X2) X0) X1 X2
               have i₂ := b18e13 X0 X2 (M.op X2 X1)
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e117 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op y x) y) X0) := by
            intro X0
            first
            | (have i₁ := b18e29 (M.op (M.op (M.op y x) y) X0)
               have i₂ := b18e13 X0 y (M.op y x)
               grind)
            | exact superpose b18e13 b18e29
            | exact resolve b18e29 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e29
          have b18e121 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b18e117 X0
               have i₂ := b18e32 X0 x y
               grind)
            | exact superpose b18e32 b18e117
            | exact resolve b18e117 b18e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e32 b18e117
          have b18e135 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b18e24
               have i₂ := b18e121 y
               grind)
            | exact superpose b18e121 b18e24
            | exact resolve b18e24 b18e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e147 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b18e135
               have i₂ := b18e121 x
               grind)
            | exact superpose b18e121 b18e135
            | exact resolve b18e135 b18e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e121 b18e135
          have b18e152 : False := by grind
          exact b18e152
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e22 : (M.op x y) ≠ (M.op x x) := by grind
            have b19e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) (M.op X2 (M.op X0 X3))) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e14 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
                 have i₂ := b19e14 X0 X2 X1
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e284 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op (M.op X0 X1) (σ x))) (M.op X1 (M.op (σ x) (σ x)))) := by
              intro X0 X1
              first
              | (have i₁ := b19e37 (σ x) X0 X1 (σ y)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e37
              | exact resolve b19e37 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e334 : (σ x) = (σ y) := by
              first
              | (have i₁ := b19e284 x x
                 have i₂ := b19e37 (σ x) x x (σ x)
                 grind)
              | exact superpose b19e37 b19e284
              | exact resolve b19e284 b19e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e37 b19e284
            have b19e388 : y = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 y
                 have i₂ := b19e334
                 grind)
              | exact superpose b19e334 b19e15
              | exact resolve b19e15 b19e334
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e334
            have b19e389 : x = y := by
              first
              | (have i₁ := b19e388
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e388
              | exact resolve b19e388 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e388
            have b19e486 : (M.op x x) ≠ (M.op x x) := by
              first
              | (have i₁ := b19e22
                 have i₂ := b19e389
                 grind)
              | exact superpose b19e389 b19e22
              | exact resolve b19e22 b19e389
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e389
            have b19e498 : False := by grind
            exact b19e498
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            have b20e25 : (M.op y y) ≠ (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) (M.op X2 (M.op X0 X3))) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
                 have i₂ := b20e14 X0 X2 X1
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e190 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op (M.op X0 X1) (σ x))) (M.op X1 (M.op (σ x) (σ x)))) := by
              intro X0 X1
              first
              | (have i₁ := b20e35 (σ x) X0 X1 (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e35
              | exact resolve b20e35 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e226 : (σ x) = (σ y) := by
              first
              | (have i₁ := b20e190 x x
                 have i₂ := b20e35 (σ x) x x (σ x)
                 grind)
              | exact superpose b20e35 b20e190
              | exact resolve b20e190 b20e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35 b20e190
            have b20e263 : y = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 y
                 have i₂ := b20e226
                 grind)
              | exact superpose b20e226 b20e15
              | exact resolve b20e15 b20e226
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e226
            have b20e264 : x = y := by
              first
              | (have i₁ := b20e263
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e263
              | exact resolve b20e263 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e263
            have b20e328 : (M.op x x) ≠ (M.op x x) := by
              first
              | (have i₁ := b20e25
                 have i₂ := b20e264
                 grind)
              | exact superpose b20e264 b20e25
              | exact resolve b20e25 b20e264
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e264
            have b20e332 : False := by grind
            exact b20e332
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e23 : y ≠ (M.op x x) := by grind
            have b21e25 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e43 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b21e17 (σ x) (σ x)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e17
              | exact resolve b21e17 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b21e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e46 : (σ y) = (k (σ x) (σ x)) := by grind
            clear b21e43
            have b21e48 : (σ y) = (σ (k x x)) := by
              first
              | (have i₁ := b21e46
                 have i₂ := b21e20 x x
                 grind)
              | exact superpose b21e20 b21e46
              | exact resolve b21e46 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e46
            have b21e50 : (σ y) = (σ (M.op x x)) := by
              first
              | (have i₁ := b21e48
                 have i₂ := b21e45 x
                 grind)
              | exact superpose b21e45 b21e48
              | exact resolve b21e48 b21e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e45 b21e48
            have b21e67 : (M.op x x) = (τ (σ y)) := by
              first
              | (have i₁ := b21e15 (M.op x x)
                 have i₂ := b21e50
                 grind)
              | exact superpose b21e50 b21e15
              | exact resolve b21e15 b21e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e50
            have b21e68 : y = (M.op x x) := by
              first
              | (have i₁ := b21e67
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e67
              | exact resolve b21e67 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e67
            have b21e71 : False := by grind
            exact b21e71
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e24 : y ≠ (M.op x x) := by grind
              have b22e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e50 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b22e18 (σ x) (σ x)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e18
                | exact resolve b22e18 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b22e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e53 : (σ y) = (k (σ x) (σ x)) := by grind
              clear b22e50
              have b22e55 : (σ y) = (σ (k x x)) := by
                first
                | (have i₁ := b22e53
                   have i₂ := b22e21 x x
                   grind)
                | exact superpose b22e21 b22e53
                | exact resolve b22e53 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e53
              have b22e58 : (σ y) = (σ (M.op x x)) := by
                first
                | (have i₁ := b22e55
                   have i₂ := b22e52 x
                   grind)
                | exact superpose b22e52 b22e55
                | exact resolve b22e55 b22e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e52 b22e55
              have b22e104 : (M.op x x) = (τ (σ y)) := by
                first
                | (have i₁ := b22e16 (M.op x x)
                   have i₂ := b22e58
                   grind)
                | exact superpose b22e58 b22e16
                | exact resolve b22e16 b22e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e58
              have b22e105 : y = (M.op x x) := by
                first
                | (have i₁ := b22e104
                   have i₂ := b22e16 y
                   grind)
                | exact superpose b22e16 b22e104
                | exact resolve b22e104 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e104
              have b22e108 : False := by grind
              exact b22e108
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e24 : y ≠ (M.op x x) := by grind
              have b23e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e50 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b23e18 (σ x) (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e18
                | exact resolve b23e18 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b23e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e53 : (σ y) = (k (σ x) (σ x)) := by grind
              clear b23e50
              have b23e54 : (σ y) = (σ (k x x)) := by
                first
                | (have i₁ := b23e53
                   have i₂ := b23e21 x x
                   grind)
                | exact superpose b23e21 b23e53
                | exact resolve b23e53 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e53
              have b23e55 : (σ y) = (σ (M.op x x)) := by
                first
                | (have i₁ := b23e54
                   have i₂ := b23e52 x
                   grind)
                | exact superpose b23e52 b23e54
                | exact resolve b23e54 b23e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e52 b23e54
              have b23e74 : (M.op x x) = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 (M.op x x)
                   have i₂ := b23e55
                   grind)
                | exact superpose b23e55 b23e16
                | exact resolve b23e16 b23e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e55
              have b23e75 : y = (M.op x x) := by
                first
                | (have i₁ := b23e74
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e74
                | exact resolve b23e74 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e74
              have b23e78 : False := by grind
              exact b23e78
        · rcases eq_or_ne (M.op y y) (M.op y x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
              intro X0 X1 X2
              grind
            have b24e22 : (M.op x y) ≠ (M.op x x) := by grind
            have b24e26 : (M.op y y) = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e34 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op y x) X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b24e14 X0 y y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e37 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X1) X2) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 (M.op (M.op (M.op X2 X1) X2) X0) X1 X2
                 have i₂ := b24e14 X0 X2 (M.op X2 X1)
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e145 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op y x) y) X0) := by
              intro X0
              first
              | (have i₁ := b24e34 (M.op (M.op (M.op y x) y) X0)
                 have i₂ := b24e14 X0 y (M.op y x)
                 grind)
              | exact superpose b24e14 b24e34
              | exact resolve b24e34 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e34
            have b24e149 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b24e145 X0
                 have i₂ := b24e37 X0 x y
                 grind)
              | exact superpose b24e37 b24e145
              | exact resolve b24e145 b24e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e37 b24e145
            have b24e163 : (M.op x y) = (M.op y x) := by
              first
              | (have i₁ := b24e26
                 have i₂ := b24e149 y
                 grind)
              | exact superpose b24e149 b24e26
              | exact resolve b24e26 b24e149
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e175 : (M.op x y) = (M.op x x) := by
              first
              | (have i₁ := b24e163
                 have i₂ := b24e149 x
                 grind)
              | exact superpose b24e149 b24e163
              | exact resolve b24e163 b24e149
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e149 b24e163
            have b24e180 : False := by grind
            exact b24e180
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b25e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b25e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e24 : y ≠ (M.op x x) := by grind
              have b25e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b25e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
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
              have b25e33 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e15 X0 y y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) (M.op X2 (M.op X0 X3))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
                   have i₂ := b25e15 X0 X2 X1
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X2 X0)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 (M.op X3 (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
                   have i₂ := b25e15 X0 (M.op X2 X1) X3
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e36 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X1) X2) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 (M.op (M.op (M.op X2 X1) X2) X0) X1 X2
                   have i₂ := b25e15 X0 X2 (M.op X2 X1)
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e38 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) := by
                intro X0
                first
                | (have i₁ := b25e33 (M.op (M.op x y) X0)
                   have i₂ := b25e15 X0 y x
                   grind)
                | exact superpose b25e15 b25e33
                | exact resolve b25e33 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e39 : ∀ X0 X1 : G, (M.op (M.op y (M.op x X0)) (M.op y (M.op X0 X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X1 (M.op y (M.op x X0)) y
                   have i₂ := b25e33 X0
                   grind)
                | exact superpose b25e33 b25e15
                | exact resolve b25e15 b25e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e41 : ∀ X0 : G, (M.op y (M.op x (M.op y X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e15 X0 y x
                   have i₂ := b25e38 X0
                   grind)
                | exact superpose b25e38 b25e15
                | exact resolve b25e15 b25e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b25e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b25e21 X0 X0
                   have i₂ := b25e55 (σ X0)
                   grind)
                | exact superpose b25e55 b25e21
                | exact resolve b25e21 b25e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e64 X0
                   have i₂ := b25e55 X0
                   grind)
                | exact superpose b25e55 b25e64
                | exact resolve b25e64 b25e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e55 b25e64
              have b25e86 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e18 X0 X1
                   have i₂ := b25e20 X0 X1
                   grind)
                | (have i₁ := b25e18 X0 X0
                   have i₂ := b25e20 X0 X1
                   grind)
                | exact superpose b25e20 b25e18
                | (have j0 := b25e18 X0 X0
                   have j1 := b25e20 X0 X1
                   grind)
                | (have r₁ := b25e18 X0 X1
                   have r₂ := b25e20 X0 X1
                   grind)
                | (have r₁ := b25e18 X1 X1
                   have r₂ := b25e20 X1 X1
                   grind)
                | (have r₁ := b25e18 X0 X1
                   have r₂ := b25e20 X0 (M.op X0 X1)
                   grind)
                | exact resolve b25e18 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b25e86 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e86
              have b25e108 : y = (M.op y (M.op x x)) := by
                first
                | (have i₁ := b25e41 y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e41
                | exact resolve b25e41 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e109 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
                intro X0
                first
                | (have i₁ := b25e41 (M.op x (M.op y X0))
                   have i₂ := b25e41 X0
                   grind)
                | exact superpose b25e41 b25e41
                | exact resolve b25e41 b25e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e110 : ∀ X0 X1 : G, (M.op y (M.op x X0)) = (M.op X1 (M.op (M.op X1 y) X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e41 (M.op X1 (M.op (M.op X1 y) X0))
                   have i₂ := b25e15 X0 y X1
                   grind)
                | exact superpose b25e15 b25e41
                | exact resolve b25e41 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e111 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y x) X0) := by
                intro X0
                first
                | (have i₁ := b25e41 (M.op (M.op y x) X0)
                   have i₂ := b25e15 X0 x y
                   grind)
                | exact superpose b25e15 b25e41
                | exact resolve b25e41 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e115 : y = (M.op x (M.op y x)) := by
                first
                | (have i₁ := b25e108
                   have i₂ := b25e109 x
                   grind)
                | exact superpose b25e109 b25e108
                | exact resolve b25e108 b25e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e108
              have b25e147 : ∀ X0 : G, (M.op x (M.op y (M.op y X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e15 X0 x y
                   have i₂ := b25e111 X0
                   grind)
                | exact superpose b25e111 b25e15
                | exact resolve b25e15 b25e111
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e184 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X3) = (M.op (M.op X0 X2) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e36 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
                   have i₂ := b25e15 X0 X2 X1
                   grind)
                | exact superpose b25e15 b25e36
                | exact resolve b25e36 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e186 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X0) X0) X2) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e36 X2 X1 X0
                   have i₂ := b25e20 X0 X1
                   grind)
                | (have i₁ := b25e36 X0 X0 X0
                   have i₂ := b25e20 X0 X1
                   grind)
                | exact superpose b25e20 b25e36
                | (have j1 := b25e20 X0 X1
                   grind)
                | exact resolve b25e36 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e196 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e36 X2 X1 (M.op X1 X0)
                   have i₂ := b25e36 (M.op X1 X0) X0 X1
                   grind)
                | exact superpose b25e36 b25e36
                | exact resolve b25e36 b25e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e200 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) (M.op X0 X1))) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X1 X2 (M.op X2 X0)
                   have i₂ := b25e36 X1 X0 X2
                   grind)
                | exact superpose b25e36 b25e15
                | exact resolve b25e15 b25e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e221 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e186 X0 X1 X2
                   have i₂ := b25e36 X2 X0 X0
                   grind)
                | exact superpose b25e36 b25e186
                | (have j0 := b25e186 X0 X1 X2
                   grind)
                | exact resolve b25e186 b25e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e186
              have b25e232 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e36 X1 (σ X0) (σ X0)
                   have i₂ := b25e65 X0
                   grind)
                | exact superpose b25e65 b25e36
                | exact resolve b25e36 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e266 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op (M.op X4 X3) X0)) = (M.op (M.op X1 (M.op (M.op X1 X2) X3)) (M.op X2 X0)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e34 X3 X1 X2 (M.op X4 (M.op (M.op X4 X3) X0))
                   have i₂ := b25e15 X0 X3 X4
                   grind)
                | exact superpose b25e15 b25e34
                | exact resolve b25e34 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e271 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op (M.op X2 X3) (M.op (M.op X4 X0) X4))) (M.op X3 (M.op X0 X1))) = X1 := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e34 (M.op (M.op X4 X0) X4) X2 X3 X1
                   have i₂ := b25e36 X1 X0 X4
                   grind)
                | exact superpose b25e36 b25e34
                | exact resolve b25e34 b25e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e273 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (M.op X1 X2) (σ X0))) (M.op X2 (σ (M.op X0 X0)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e34 (σ X0) X1 X2 (σ X0)
                   have i₂ := b25e65 X0
                   grind)
                | exact superpose b25e65 b25e34
                | exact resolve b25e34 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e275 : ∀ X0 X1 X2 : G, (M.op y (M.op y X0)) = (M.op (M.op X1 (M.op (M.op X1 X2) x)) (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e34 x X1 X2 (M.op y (M.op y X0))
                   have i₂ := b25e147 X0
                   grind)
                | exact superpose b25e147 b25e34
                | exact resolve b25e34 b25e147
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e278 : ∀ X0 X1 X2 : G, (M.op x (M.op y X0)) = (M.op (M.op X1 (M.op (M.op X1 X2) y)) (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e34 y X1 X2 (M.op x (M.op y X0))
                   have i₂ := b25e41 X0
                   grind)
                | exact superpose b25e41 b25e34
                | exact resolve b25e34 b25e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e292 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X1 X0)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 (M.op X2 (M.op X3 X0)) (M.op (M.op X1 X2) X3) X1
                   have i₂ := b25e34 X3 X1 X2 X0
                   grind)
                | exact superpose b25e34 b25e15
                | exact resolve b25e15 b25e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e320 : ∀ X0 X2 : G, (M.op x (M.op y X0)) = (M.op (M.op y X2) (M.op X2 X0)) := by
                intro X0 X2
                first
                | (have i₁ := b25e278 X0 x X2
                   have i₂ := b25e184 y x X2 (M.op X2 X0)
                   grind)
                | exact superpose b25e184 b25e278
                | exact resolve b25e278 b25e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e278
              have b25e323 : ∀ X0 X2 : G, (M.op y (M.op y X0)) = (M.op (M.op x X2) (M.op X2 X0)) := by
                intro X0 X2
                first
                | (have i₁ := b25e275 X0 x X2
                   have i₂ := b25e184 x x X2 (M.op X2 X0)
                   grind)
                | exact superpose b25e184 b25e275
                | exact resolve b25e275 b25e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e275
              have b25e325 : ∀ X0 X2 : G, (σ X0) = (M.op (M.op (σ X0) X2) (M.op X2 (σ (M.op X0 X0)))) := by
                intro X0 X2
                first
                | (have i₁ := b25e273 X0 x X2
                   have i₂ := b25e184 (σ X0) x X2 (M.op X2 (σ (M.op X0 X0)))
                   grind)
                | exact superpose b25e184 b25e273
                | exact resolve b25e273 b25e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e273
              have b25e327 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X4 X0) X4) X3) (M.op X3 (M.op X0 X1))) = X1 := by
                intro X0 X1 X3 X4
                first
                | (have i₁ := b25e271 X0 X1 x X3 X4
                   have i₂ := b25e184 (M.op (M.op X4 X0) X4) x X3 (M.op X3 (M.op X0 X1))
                   grind)
                | exact superpose b25e184 b25e271
                | exact resolve b25e271 b25e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e271
              have b25e332 : ∀ X0 X2 X3 X4 : G, (M.op X4 (M.op (M.op X4 X3) X0)) = (M.op (M.op X3 X2) (M.op X2 X0)) := by
                intro X0 X2 X3 X4
                first
                | (have i₁ := b25e266 X0 x X2 X3 X4
                   have i₂ := b25e184 X3 x X2 (M.op X2 X0)
                   grind)
                | exact superpose b25e184 b25e266
                | exact resolve b25e266 b25e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e266
              have b25e365 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X3 (M.op X0 X1))) = X1 := by
                intro X0 X1 X3
                first
                | (have i₁ := b25e327 X0 X1 X3 x
                   have i₂ := b25e36 X3 X0 x
                   grind)
                | exact superpose b25e36 b25e327
                | exact resolve b25e327 b25e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e327
              have b25e390 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 (M.op X1 X0)) X4)) = (M.op X3 (M.op (M.op X0 (M.op X1 X2)) X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e35 X4 X2 (M.op X3 (M.op X1 X0)) X3
                   have i₂ := b25e35 X2 X0 X1 X3
                   grind)
                | exact superpose b25e35 b25e35
                | exact resolve b25e35 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e393 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X3)) (M.op X0 X4)) = (M.op (M.op X3 X0) (M.op X2 X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e35 X4 (M.op X3 X0) X2 (M.op X1 (M.op (M.op X1 X2) X3))
                   have i₂ := b25e34 X3 X1 X2 X0
                   grind)
                | exact superpose b25e34 b25e35
                | exact resolve b25e35 b25e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e398 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op x X0) (M.op y X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e35 X1 (M.op x X0) y y
                   have i₂ := b25e33 X0
                   grind)
                | exact superpose b25e33 b25e35
                | exact resolve b25e35 b25e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e399 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op y X0) (M.op x X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e35 X1 (M.op y X0) x y
                   have i₂ := b25e41 X0
                   grind)
                | exact superpose b25e41 b25e35
                | exact resolve b25e35 b25e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e41
              have b25e417 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 (M.op X1 X0)) X2) = (M.op (M.op X3 (M.op (M.op X3 X4) X5)) (M.op X4 (M.op X0 (M.op X1 X2)))) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b25e34 X5 X3 X4 (M.op (M.op X5 (M.op X1 X0)) X2)
                   have i₂ := b25e35 X2 X0 X1 X5
                   grind)
                | exact superpose b25e35 b25e34
                | exact resolve b25e34 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e34
              have b25e422 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X4 X3) (M.op X1 X0)) X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e15 (M.op (M.op (M.op X4 X3) (M.op X1 X0)) X2) X3 X4
                   have i₂ := b25e35 X2 X0 X1 (M.op X4 X3)
                   grind)
                | exact superpose b25e35 b25e15
                | exact resolve b25e15 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e424 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op X1 X0)) X2) = (M.op y (M.op y (M.op X0 (M.op X1 X2)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e33 (M.op (M.op x (M.op X1 X0)) X2)
                   have i₂ := b25e35 X2 X0 X1 x
                   grind)
                | exact superpose b25e35 b25e33
                | exact resolve b25e33 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e425 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X1 X0)) X2) = (M.op x (M.op y (M.op X0 (M.op X1 X2)))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e147 (M.op (M.op y (M.op X1 X0)) X2)
                   have i₂ := b25e35 X2 X0 X1 y
                   grind)
                | exact superpose b25e35 b25e147
                | exact resolve b25e147 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e147
              have b25e433 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X5 (M.op X1 X0)) X2) = (M.op (M.op X5 X4) (M.op X4 (M.op X0 (M.op X1 X2)))) := by
                intro X0 X1 X2 X4 X5
                first
                | (have i₁ := b25e417 X0 X1 X2 x X4 X5
                   have i₂ := b25e184 X5 x X4 (M.op X4 (M.op X0 (M.op X1 X2)))
                   grind)
                | exact superpose b25e184 b25e417
                | exact resolve b25e417 b25e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e417
              have b25e448 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op X0 X4)) = (M.op (M.op X3 X0) (M.op X2 X4)) := by
                intro X0 X2 X3 X4
                first
                | (have i₁ := b25e393 X0 x X2 X3 X4
                   have i₂ := b25e184 X3 x X2 (M.op X0 X4)
                   grind)
                | exact superpose b25e184 b25e393
                | exact resolve b25e393 b25e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e393
              have b25e617 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b25e91 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e91
              have b25e620 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b25e617 X0 X1
                   have j1 := b25e221 X0 X1 x
                   grind)
                | (have r₁ := b25e617 x X0
                   have r₂ := b25e221 X0 x x
                   grind)
                | (have r₁ := b25e617 x X1
                   have r₂ := b25e221 x X1 x
                   grind)
                | (have r₁ := b25e617 X0 X1
                   have r₂ := b25e221 X0 (M.op X1 X0) x
                   grind)
                | exact resolve b25e617 b25e221
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e221 b25e617
              have b25e785 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e196 (σ X0) (σ X0) X1
                   have i₂ := b25e65 X0
                   grind)
                | exact superpose b25e65 b25e196
                | exact resolve b25e196 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e797 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X0 X2)))) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e196 (M.op X2 (M.op X0 X2)) X1 X3
                   have i₂ := b25e196 X2 X0 (M.op X1 (M.op X2 (M.op X0 X2)))
                   grind)
                | exact superpose b25e196 b25e196
                | exact resolve b25e196 b25e196
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e992 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b25e200 (σ X0) (σ X0) X1
                   have i₂ := b25e65 X0
                   grind)
                | exact superpose b25e65 b25e200
                | exact resolve b25e200 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e1017 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X3)) = (M.op (M.op X2 X0) (M.op (M.op X1 X2) X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e35 X3 (M.op X2 X0) (M.op X1 X2) X1
                   have i₂ := b25e200 X2 X0 X1
                   grind)
                | exact superpose b25e200 b25e35
                | exact resolve b25e35 b25e200
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e1025 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e36 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X1
                   have i₂ := b25e200 X2 X0 X1
                   grind)
                | exact superpose b25e200 b25e36
                | exact resolve b25e36 b25e200
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e1053 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e1025 X0 X1 X2 X3
                   have i₂ := b25e422 X0 X2 X3 X2 X1
                   grind)
                | exact superpose b25e422 b25e1025
                | exact resolve b25e1025 b25e422
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1025
              have b25e1391 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y (M.op (M.op x (M.op y X0)) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e35 X1 X0 x y
                   have i₂ := b25e109 X0
                   grind)
                | exact superpose b25e109 b25e35
                | exact resolve b25e35 b25e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e1408 : ∀ X0 X1 : G, (M.op y (M.op (M.op x (M.op y X0)) (M.op (M.op x X0) X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e200 (M.op x X0) X1 y
                   have i₂ := b25e109 X0
                   grind)
                | exact superpose b25e109 b25e200
                | exact resolve b25e200 b25e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e1413 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 (M.op y y)) (M.op (M.op x X0) X1))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e1408 X0 X1
                   have i₂ := b25e390 X0 y y x (M.op (M.op x X0) X1)
                   grind)
                | (have i₁ := b25e1408 x X1
                   have i₂ := b25e390 x y x y (M.op (M.op x x) X1)
                   grind)
                | exact superpose b25e390 b25e1408
                | exact resolve b25e1408 b25e390
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1408
              have b25e1424 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op x (M.op (M.op X0 (M.op y y)) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e1391 X0 X1
                   have i₂ := b25e390 X0 y y x X1
                   grind)
                | (have i₁ := b25e1391 x x
                   have i₂ := b25e390 x y x y x
                   grind)
                | exact superpose b25e390 b25e1391
                | exact resolve b25e1391 b25e390
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1391
              have b25e1436 : ∀ X1 : G, (M.op x (M.op x (M.op (M.op y y) X1))) = X1 := by
                intro X1
                first
                | (have i₁ := b25e1413 x X1
                   have i₂ := b25e1017 (M.op y y) x x X1
                   grind)
                | exact superpose b25e1017 b25e1413
                | exact resolve b25e1413 b25e1017
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1017 b25e1413
              have b25e1445 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op x (M.op (M.op X0 x) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e1424 X0 X1
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e1424
                | exact resolve b25e1424 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1424
              have b25e1451 : ∀ X1 : G, (M.op x (M.op x (M.op x X1))) = X1 := by
                intro X1
                first
                | (have i₁ := b25e1436 X1
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e1436
                | exact resolve b25e1436 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1436
              have b25e1639 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x (M.op x X0)) := by
                intro X0
                first
                | (have i₁ := b25e33 (M.op x (M.op x X0))
                   have i₂ := b25e1451 X0
                   grind)
                | exact superpose b25e1451 b25e33
                | exact resolve b25e33 b25e1451
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e33
              have b25e1640 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x x) X0) := by
                intro X0
                first
                | (have i₁ := b25e365 x (M.op x X0) x
                   have i₂ := b25e1451 X0
                   grind)
                | exact superpose b25e1451 b25e365
                | exact resolve b25e365 b25e1451
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e1641 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x X0) (M.op x X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e35 X1 (M.op x X0) x x
                   have i₂ := b25e1451 X0
                   grind)
                | exact superpose b25e1451 b25e35
                | exact resolve b25e35 b25e1451
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e1648 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op x (M.op x X0)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e36 X1 (M.op x (M.op x X0)) x
                   have i₂ := b25e1451 X0
                   grind)
                | exact superpose b25e1451 b25e36
                | exact resolve b25e36 b25e1451
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1451
              have b25e2438 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b25e26
                   have i₂ := b25e620 (σ x) X0
                   grind)
                | (have i₁ := b25e26
                   have i₂ := b25e620 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b25e620 b25e26
                | (have j1 := b25e620 (σ x) X0
                   grind)
                | (have r₁ := b25e26
                   have r₂ := b25e620 (σ x) (σ y)
                   grind)
                | exact resolve b25e26 b25e620
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e2439 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e65 X1
                   have i₂ := b25e620 (σ X1) X0
                   grind)
                | (have i₁ := b25e65 X0
                   have i₂ := b25e620 X0 (M.op (σ X0) (σ X0))
                   grind)
                | exact superpose b25e620 b25e65
                | (have j1 := b25e620 (σ X1) X0
                   grind)
                | exact resolve b25e65 b25e620
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e2710 : ∀ X0 : G, x = X0 ∨ (k (M.op y (M.op x x)) X0) = (M.op X0 (M.op y (M.op x x))) := by
                intro X0
                first
                | (have i₁ := b25e620 (M.op y (M.op x x)) X0
                   have i₂ := b25e39 x x
                   grind)
                | exact superpose b25e39 b25e620
                | (have j0 := b25e620 (M.op y (M.op x x)) X0
                   grind)
                | exact resolve b25e620 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e2742 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = (k (M.op x (M.op y x)) X0) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e2710 X0
                   have i₂ := b25e109 x
                   grind)
                | exact superpose b25e109 b25e2710
                | (have j0 := b25e2710 X0
                   grind)
                | exact resolve b25e2710 b25e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2710
              have b25e2808 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e2742 X0
                   have i₂ := b25e115
                   grind)
                | exact superpose b25e115 b25e2742
                | (have j0 := b25e2742 X0
                   grind)
                | exact resolve b25e2742 b25e115
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2742
              have b25e2946 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X2)) = (M.op y (M.op (M.op (M.op x X1) (M.op X1 X0)) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e398 (M.op (M.op x X1) (M.op X1 X0)) X2
                   have i₂ := b25e200 X1 X0 x
                   grind)
                | exact superpose b25e200 b25e398
                | exact resolve b25e398 b25e200
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e2954 : ∀ X0 X1 : G, (M.op y (M.op X1 (M.op x X0))) = (M.op (M.op x X1) (M.op x (M.op y X0))) := by
                intro X0 X1
                first
                | (have i₁ := b25e398 X1 (M.op x X0)
                   have i₂ := b25e109 X0
                   grind)
                | exact superpose b25e109 b25e398
                | exact resolve b25e398 b25e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e2955 : ∀ X0 X1 : G, (M.op y (M.op X1 (M.op y X0))) = (M.op (M.op x X1) (M.op x (M.op x X0))) := by
                intro X0 X1
                first
                | (have i₁ := b25e398 X1 (M.op y X0)
                   have i₂ := b25e1639 X0
                   grind)
                | exact superpose b25e1639 b25e398
                | exact resolve b25e398 b25e1639
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e2982 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y (M.op (M.op X0 x) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e196 x X0 (M.op y X1)
                   have i₂ := b25e398 (M.op X0 x) X1
                   grind)
                | exact superpose b25e398 b25e196
                | exact resolve b25e196 b25e398
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e398
              have b25e3035 : ∀ X0 X1 : G, (M.op y (M.op X1 (M.op y X0))) = (M.op x (M.op X1 (M.op x X0))) := by
                intro X0 X1
                first
                | (have i₁ := b25e2955 X0 X1
                   have i₂ := b25e1641 X1 (M.op x X0)
                   grind)
                | exact superpose b25e1641 b25e2955
                | exact resolve b25e2955 b25e1641
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2955
              have b25e3036 : ∀ X0 X1 : G, (M.op y (M.op X1 (M.op x X0))) = (M.op x (M.op X1 (M.op y X0))) := by
                intro X0 X1
                first
                | (have i₁ := b25e2954 X0 X1
                   have i₂ := b25e1641 X1 (M.op y X0)
                   grind)
                | exact superpose b25e1641 b25e2954
                | exact resolve b25e2954 b25e1641
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1641 b25e2954
              have b25e3039 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X2)) = (M.op y (M.op X1 (M.op x (M.op X0 (M.op X1 X2))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e2946 X0 X1 X2
                   have i₂ := b25e422 X0 X1 X2 X1 x
                   grind)
                | exact superpose b25e422 b25e2946
                | exact resolve b25e2946 b25e422
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2946
              have b25e3057 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X2)) = (M.op x (M.op X1 (M.op y (M.op X0 (M.op X1 X2))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e3039 X0 X1 X2
                   have i₂ := b25e3036 (M.op X0 (M.op X1 X2)) X1
                   grind)
                | exact superpose b25e3036 b25e3039
                | exact resolve b25e3039 b25e3036
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3036 b25e3039
              have b25e3065 : ∀ X0 X2 : G, (M.op X0 (M.op y X2)) = (M.op x (M.op (M.op X0 y) X2)) := by
                intro X0 X2
                first
                | (have i₁ := b25e3057 X0 x X2
                   have i₂ := b25e1053 X0 y x X2
                   grind)
                | exact superpose b25e1053 b25e3057
                | exact resolve b25e3057 b25e1053
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1053 b25e3057
              have b25e3077 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
                intro X0
                first
                | (have i₁ := b25e32 X0 y
                   have i₂ := b25e2808 (τ X0)
                   grind)
                | exact superpose b25e2808 b25e32
                | (have j1 := b25e2808 (τ X0)
                   grind)
                | exact resolve b25e32 b25e2808
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e32 b25e2808
              have b25e4246 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X3)) X4) = (M.op (M.op X3 (M.op X2 (M.op X1 X0))) X4) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e184 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0)) X4
                   have i₂ := b25e365 X1 X0 X2
                   grind)
                | exact superpose b25e365 b25e184
                | exact resolve b25e184 b25e365
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e4330 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X0 (M.op (M.op X3 X1) X2)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e35 X2 X0 (M.op X3 X1) X3
                   have i₂ := b25e184 X0 X3 X1 X2
                   grind)
                | exact superpose b25e184 b25e35
                | exact resolve b25e35 b25e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e4454 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 (M.op X1 X0))) X4) = (M.op X2 (M.op X1 (M.op X3 (M.op X0 X4)))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e4246 X0 X1 X2 X3 X4
                   have i₂ := b25e422 X3 X0 X4 X2 X1
                   grind)
                | exact superpose b25e422 b25e4246
                | exact resolve b25e4246 b25e422
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4246
              have b25e4538 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b25e2438 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2438
              have b25e4539 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b25e4538
                   have i₂ := b25e21 x y
                   grind)
                | exact superpose b25e21 b25e4538
                | exact resolve b25e4538 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4538
              have b25e5166 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X3 X4)) = (M.op (M.op X0 X3) (M.op (M.op X2 X1) X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e292 X4 (M.op X2 X1) (M.op X1 (M.op X2 X0)) X3
                   have i₂ := b25e365 X2 X0 X1
                   grind)
                | exact superpose b25e365 b25e292
                | exact resolve b25e292 b25e365
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e5254 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op y X0) X1) x) := by
                intro X0 X1
                first
                | (have i₁ := b25e292 y y X0 X1
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e292
                | exact resolve b25e292 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e5536 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 x) X2)) = (M.op y (M.op (M.op X0 (M.op y X1)) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e35 X2 X1 (M.op X0 x) y
                   have i₂ := b25e2982 X0 X1
                   grind)
                | exact superpose b25e2982 b25e35
                | exact resolve b25e35 b25e2982
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e7315 : ∀ X0 : G, (M.op (M.op y X0) x) = (M.op x (M.op X0 y)) := by
                intro X0
                first
                | (have i₁ := b25e5254 x X0
                   have i₂ := b25e111 X0
                   grind)
                | exact superpose b25e111 b25e5254
                | exact resolve b25e5254 b25e111
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e111
              have b25e7317 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op (M.op X0 y) (M.op X1 y)) := by
                intro X0 X1
                first
                | (have i₁ := b25e5254 (M.op X0 y) X1
                   have i₂ := b25e196 y X0 X1
                   grind)
                | exact superpose b25e196 b25e5254
                | exact resolve b25e5254 b25e196
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e7350 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x X2)) = (M.op (M.op X0 (M.op X1 y)) (M.op (M.op y X0) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e292 X2 (M.op y X0) X1 x
                   have i₂ := b25e5254 X0 X1
                   grind)
                | exact superpose b25e5254 b25e292
                | exact resolve b25e292 b25e5254
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e7421 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x X2)) = (M.op y (M.op (M.op (M.op X0 (M.op X1 y)) X0) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e7350 X0 X1 X2
                   have i₂ := b25e4330 y X0 X2 (M.op X0 (M.op X1 y))
                   grind)
                | (have i₁ := b25e7350 X0 X1 X2
                   have i₂ := b25e4330 (M.op X0 (M.op X1 y)) X0 X2 y
                   grind)
                | exact superpose b25e4330 b25e7350
                | exact resolve b25e7350 b25e4330
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e7350
              have b25e7473 : ∀ X1 X2 : G, (M.op X1 (M.op x X2)) = (M.op y (M.op (M.op X1 y) X2)) := by
                intro X1 X2
                first
                | (have i₁ := b25e7421 x X1 X2
                   have i₂ := b25e36 X2 (M.op X1 y) x
                   grind)
                | exact superpose b25e36 b25e7421
                | exact resolve b25e7421 b25e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e7421
              have b25e7781 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op y X0) X2)) = (M.op X1 (M.op (M.op X1 (M.op x (M.op X0 y))) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e35 X2 x (M.op y X0) X1
                   have i₂ := b25e7315 X0
                   grind)
                | exact superpose b25e7315 b25e35
                | exact resolve b25e35 b25e7315
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e7315
              have b25e7825 : ∀ X0 X2 : G, (M.op x (M.op (M.op y X0) X2)) = (M.op (M.op X0 y) (M.op x X2)) := by
                intro X0 X2
                first
                | (have i₁ := b25e7781 X0 x X2
                   have i₂ := b25e35 X2 (M.op X0 y) x x
                   grind)
                | exact superpose b25e35 b25e7781
                | exact resolve b25e7781 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e7781
              have b25e7871 : ∀ X0 X2 : G, (M.op x (M.op (M.op y X0) X2)) = (M.op (M.op X0 x) (M.op y X2)) := by
                intro X0 X2
                first
                | (have i₁ := b25e7825 X0 X2
                   have i₂ := b25e448 x y X0 X2
                   grind)
                | (have i₁ := b25e7825 X0 X2
                   have i₂ := b25e448 y x X0 X2
                   grind)
                | exact superpose b25e448 b25e7825
                | exact resolve b25e7825 b25e448
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e7825
              have b25e7991 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 x)) = (M.op (M.op y X0) (M.op X0 (M.op X1 y))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e332 x X2 X1 (M.op y X0)
                   have i₂ := b25e5254 X0 X1
                   grind)
                | exact superpose b25e5254 b25e332
                | exact resolve b25e332 b25e5254
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e8124 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) y)) = (M.op (M.op X1 y) x) := by
                intro X0 X1
                first
                | (have i₁ := b25e332 y y X1 X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e332
                | exact resolve b25e332 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e8496 : ∀ X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 x)) = (M.op x (M.op y (M.op X1 y))) := by
                intro X1 X2
                first
                | (have i₁ := b25e7991 x X1 X2
                   have i₂ := b25e320 (M.op X1 y) x
                   grind)
                | exact superpose b25e320 b25e7991
                | exact resolve b25e7991 b25e320
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e320 b25e7991
              have b25e8873 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op (M.op X0 X1) y) x) := by
                intro X0 X1
                first
                | (have i₁ := b25e35 y X1 X0 x
                   have i₂ := b25e8124 x (M.op X0 X1)
                   grind)
                | exact superpose b25e8124 b25e35
                | exact resolve b25e35 b25e8124
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35 b25e8124
              have b25e13183 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) (M.op (σ X0) X2)) = (M.op (σ (M.op X0 X0)) (M.op X1 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e448 (σ X0) X1 (σ X0) X2
                   have i₂ := b25e65 X0
                   grind)
                | exact superpose b25e65 b25e448
                | exact resolve b25e448 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e21560 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op X1 y))) = (M.op x (M.op (M.op X0 X1) x)) := by
                intro X0 X1
                first
                | (have i₁ := b25e3065 X0 (M.op X1 y)
                   have i₂ := b25e7317 X0 X1
                   grind)
                | exact superpose b25e7317 b25e3065
                | exact resolve b25e3065 b25e7317
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e7317
              have b25e24768 : ∀ X0 : G, (M.op (M.op y X0) (M.op x x)) = (M.op y (M.op X0 (M.op y y))) := by
                intro X0
                first
                | (have i₁ := b25e7473 (M.op y X0) x
                   have i₂ := b25e5254 X0 y
                   grind)
                | exact superpose b25e5254 b25e7473
                | exact resolve b25e7473 b25e5254
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e5254 b25e7473
              have b25e24985 : ∀ X0 : G, (M.op (M.op y X0) (M.op x x)) = (M.op x (M.op X0 (M.op x y))) := by
                intro X0
                first
                | (have i₁ := b25e24768 X0
                   have i₂ := b25e3035 y X0
                   grind)
                | exact superpose b25e3035 b25e24768
                | exact resolve b25e24768 b25e3035
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3035 b25e24768
              have b25e25053 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op x (M.op X0 (M.op x y))) := by
                intro X0
                first
                | (have i₁ := b25e24985 X0
                   have i₂ := b25e399 X0 x
                   grind)
                | exact superpose b25e399 b25e24985
                | exact resolve b25e24985 b25e399
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e399 b25e24985
              have b25e31265 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X1 y))) = (M.op (M.op X1 X0) (M.op y x)) := by
                intro X0 X1
                first
                | (have i₁ := b25e3065 (M.op X1 X0) x
                   have i₂ := b25e8873 X1 X0
                   grind)
                | exact superpose b25e8873 b25e3065
                | exact resolve b25e3065 b25e8873
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3065 b25e8873
              have b25e31956 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op (M.op (M.op X1 (M.op X0 X2)) (M.op y X3)) X4)) = (M.op X3 (M.op (M.op (M.op x (M.op X0 X1)) X2) X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e390 (M.op X1 (M.op X0 X2)) y X3 y X4
                   have i₂ := b25e424 X1 X0 X2
                   grind)
                | exact superpose b25e424 b25e390
                | exact resolve b25e390 b25e424
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e32668 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X3 X4)) X5)) = (M.op (M.op X1 (M.op X4 (M.op X3 X0))) (M.op X2 X5)) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b25e448 (M.op X4 (M.op X3 X0)) X2 X1 X5
                   have i₂ := b25e390 X4 X3 X0 (M.op X1 X2) X5
                   grind)
                | (have i₁ := b25e448 (M.op X3 (M.op X1 X0)) X2 X3 X4
                   have i₂ := b25e390 X0 X1 (M.op X3 X2) X3 X4
                   grind)
                | exact superpose b25e390 b25e448
                | exact resolve b25e448 b25e390
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e390 b25e448
              have b25e32816 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X3 X4)) X5)) = (M.op X4 (M.op X3 (M.op X1 (M.op X0 (M.op X2 X5))))) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b25e32668 X0 X1 X2 X3 X4 X5
                   have i₂ := b25e4454 X0 X3 X4 X1 (M.op X2 X5)
                   grind)
                | exact superpose b25e4454 b25e32668
                | exact resolve b25e32668 b25e4454
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4454 b25e32668
              have b25e33353 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op x (M.op X0 X1)) X2) X4)) = (M.op X3 (M.op (M.op (M.op X1 (M.op X0 X2)) x) X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e31956 X0 X1 X2 X3 X4
                   have i₂ := b25e5536 (M.op X1 (M.op X0 X2)) X3 X4
                   grind)
                | exact superpose b25e5536 b25e31956
                | exact resolve b25e31956 b25e5536
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e5536 b25e31956
              have b25e33534 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op X3 (M.op X1 (M.op X0 (M.op X2 X5))))) = (M.op X0 (M.op X2 (M.op X1 (M.op X4 (M.op X3 X5))))) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b25e32816 X4 X1 X3 X2 X0 X5
                   have i₂ := b25e422 X0 X2 X5 X3 X1
                   grind)
                | exact superpose b25e422 b25e32816
                | exact resolve b25e32816 b25e422
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e422 b25e32816
              have b25e43339 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 y) X0)) = (M.op (M.op X1 X4) (M.op X4 (M.op X3 (M.op y (M.op x X0))))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e433 X3 X2 (M.op (M.op X2 y) X0) X4 X1
                   have i₂ := b25e110 X0 X2
                   grind)
                | exact superpose b25e110 b25e433
                | exact resolve b25e433 b25e110
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e110
              have b25e43424 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op y X2)) (M.op x X0)) = (M.op (M.op X1 X3) (M.op X3 (M.op X2 (M.op x (M.op y X0))))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e433 X2 y (M.op x X0) X3 X1
                   have i₂ := b25e109 X0
                   grind)
                | exact superpose b25e109 b25e433
                | exact resolve b25e433 b25e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e433
              have b25e44098 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op y X2)) (M.op x X0)) = (M.op x (M.op y (M.op X2 (M.op (M.op X1 X3) (M.op X3 X0))))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e43424 X0 X1 X2 X3
                   have i₂ := b25e33534 x X2 y X3 (M.op X1 X3) X0
                   grind)
                | (have i₁ := b25e43424 X0 X1 X2 X3
                   have i₂ := b25e33534 (M.op X1 X3) X2 X3 y x X0
                   grind)
                | exact superpose b25e33534 b25e43424
                | exact resolve b25e43424 b25e33534
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e43424
              have b25e44165 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 y) X0)) = (M.op y (M.op x (M.op X3 (M.op (M.op X1 X4) (M.op X4 X0))))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e43339 X0 X1 X2 X3 X4
                   have i₂ := b25e33534 y X3 x X4 (M.op X1 X4) X0
                   grind)
                | (have i₁ := b25e43339 X0 X1 X2 X3 X4
                   have i₂ := b25e33534 (M.op X1 X4) X3 X4 x y X0
                   grind)
                | exact superpose b25e33534 b25e43339
                | exact resolve b25e43339 b25e33534
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e33534 b25e43339
              have b25e44452 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op y X2)) (M.op x X0)) = (M.op (M.op y (M.op (M.op X1 X3) X2)) (M.op X3 X0)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e44098 X0 X1 X2 X3
                   have i₂ := b25e425 X2 (M.op X1 X3) (M.op X3 X0)
                   grind)
                | exact superpose b25e425 b25e44098
                | exact resolve b25e44098 b25e425
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e44098
              have b25e44504 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 y) X0)) = (M.op x (M.op y (M.op X3 (M.op (M.op X1 X4) (M.op X4 X0))))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e44165 X0 X1 X2 X3 X4
                   have i₂ := b25e109 (M.op X3 (M.op (M.op X1 X4) (M.op X4 X0)))
                   grind)
                | exact superpose b25e109 b25e44165
                | exact resolve b25e44165 b25e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e44165
              have b25e44713 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op y X2)) (M.op x X0)) = (M.op (M.op X2 X3) (M.op (M.op (M.op X1 X3) y) X0)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e44452 X0 X1 X2 X3
                   have i₂ := b25e5166 X2 y (M.op X1 X3) X3 X0
                   grind)
                | (have i₁ := b25e44452 x X1 X2 (M.op X2 X1)
                   have i₂ := b25e5166 y X1 X2 (M.op (M.op X1 (M.op X2 X1)) X2) x
                   grind)
                | exact superpose b25e5166 b25e44452
                | exact resolve b25e44452 b25e5166
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e44452
              have b25e44752 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 y) X0)) = (M.op (M.op y (M.op (M.op X1 X4) X3)) (M.op X4 X0)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e44504 X0 X1 X2 X3 X4
                   have i₂ := b25e425 X3 (M.op X1 X4) (M.op X4 X0)
                   grind)
                | exact superpose b25e425 b25e44504
                | exact resolve b25e44504 b25e425
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e425 b25e44504
              have b25e44867 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X1 X3) y) X0)) = (M.op (M.op X2 x) (M.op (M.op y X1) X0)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e44713 X0 X1 X2 X3
                   have i₂ := b25e5166 X2 X1 y x X0
                   grind)
                | exact superpose b25e5166 b25e44713
                | exact resolve b25e44713 b25e5166
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e44713
              have b25e44881 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 y) X0)) = (M.op (M.op X3 X4) (M.op (M.op (M.op X1 X4) y) X0)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e44752 X0 X1 X2 X3 X4
                   have i₂ := b25e5166 X3 y (M.op X1 X4) X4 X0
                   grind)
                | (have i₁ := b25e44752 X4 X1 X2 X3 (M.op X2 X1)
                   have i₂ := b25e5166 y X1 X2 (M.op (M.op X1 (M.op X2 X1)) X3) X4
                   grind)
                | exact superpose b25e5166 b25e44752
                | exact resolve b25e44752 b25e5166
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e5166 b25e44752
              have b25e44955 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X1 X3) y) X0)) = (M.op y (M.op (M.op (M.op X2 x) X1) X0)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e44867 X0 X1 X2 X3
                   have i₂ := b25e4330 y X1 X0 (M.op X2 x)
                   grind)
                | (have i₁ := b25e44867 X0 X1 X2 X3
                   have i₂ := b25e4330 (M.op X2 x) X1 X0 y
                   grind)
                | exact superpose b25e4330 b25e44867
                | exact resolve b25e44867 b25e4330
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e44867
              have b25e44959 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op (M.op X1 (M.op X2 X3)) y) X0)) = (M.op (M.op X3 X4) (M.op (M.op (M.op X1 X4) y) X0)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e44881 X0 X1 X2 X3 X4
                   have i₂ := b25e4330 X2 y X0 (M.op X1 (M.op X2 X3))
                   grind)
                | (have i₁ := b25e44881 X0 X1 X2 X3 X4
                   have i₂ := b25e4330 (M.op X1 (M.op X2 X3)) y X0 X2
                   grind)
                | exact superpose b25e4330 b25e44881
                | exact resolve b25e44881 b25e4330
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4330 b25e44881
              have b25e45006 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X1 (M.op X2 X3)) y) X0)) = (M.op y (M.op (M.op (M.op X3 x) X1) X0)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e44959 X0 X1 X2 X3 x
                   have i₂ := b25e44955 X0 X1 X3 x
                   grind)
                | exact superpose b25e44955 b25e44959
                | exact resolve b25e44959 b25e44955
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e44955 b25e44959
              have b25e67843 : ∀ X0 : G, (M.op y (M.op y (M.op X0 (M.op x y)))) = (M.op (M.op x x) (M.op y (M.op X0 x))) := by
                intro X0
                first
                | (have i₁ := b25e323 (M.op X0 (M.op x y)) x
                   have i₂ := b25e25053 X0
                   grind)
                | exact superpose b25e25053 b25e323
                | exact resolve b25e323 b25e25053
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e323
              have b25e68255 : ∀ X0 : G, (M.op y (M.op y (M.op X0 (M.op x y)))) = (M.op x (M.op (M.op y x) (M.op X0 x))) := by
                intro X0
                first
                | (have i₁ := b25e67843 X0
                   have i₂ := b25e7871 x (M.op X0 x)
                   grind)
                | exact superpose b25e7871 b25e67843
                | exact resolve b25e67843 b25e7871
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e7871 b25e67843
              have b25e68488 : ∀ X0 : G, (M.op y (M.op y (M.op X0 (M.op x y)))) = (M.op y (M.op x (M.op X0 x))) := by
                intro X0
                first
                | (have i₁ := b25e68255 X0
                   have i₂ := b25e1445 y (M.op X0 x)
                   grind)
                | exact superpose b25e1445 b25e68255
                | exact resolve b25e68255 b25e1445
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1445 b25e68255
              have b25e68666 : ∀ X0 : G, (M.op y (M.op y (M.op X0 (M.op x y)))) = (M.op x (M.op y (M.op X0 x))) := by
                intro X0
                first
                | (have i₁ := b25e68488 X0
                   have i₂ := b25e109 (M.op X0 x)
                   grind)
                | exact superpose b25e109 b25e68488
                | exact resolve b25e68488 b25e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e68488
              have b25e68784 : ∀ X0 : G, (M.op (M.op x (M.op x X0)) y) = (M.op x (M.op y (M.op X0 x))) := by
                intro X0
                first
                | (have i₁ := b25e68666 X0
                   have i₂ := b25e424 X0 x y
                   grind)
                | exact superpose b25e424 b25e68666
                | exact resolve b25e68666 b25e424
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e424 b25e68666
              have b25e68854 : ∀ X0 : G, (M.op (M.op X0 x) y) = (M.op x (M.op y (M.op X0 x))) := by
                intro X0
                first
                | (have i₁ := b25e68784 X0
                   have i₂ := b25e1648 X0 y
                   grind)
                | exact superpose b25e1648 b25e68784
                | exact resolve b25e68784 b25e1648
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1648 b25e68784
              have b25e108786 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
                intro X0
                first
                | (have i₁ := b25e232 y X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e232
                | exact resolve b25e232 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e232
              have b25e111776 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) (σ x)) X0) := by
                intro X0
                first
                | (have i₁ := b25e36 X0 (σ y) (σ x)
                   have i₂ := b25e108786 (σ x)
                   grind)
                | exact superpose b25e108786 b25e36
                | exact resolve b25e36 b25e108786
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e111777 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e15 X0 (σ y) (σ x)
                   have i₂ := b25e108786 X0
                   grind)
                | exact superpose b25e108786 b25e15
                | exact resolve b25e15 b25e108786
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e111793 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 (σ x)) X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e332 X0 (σ y) (σ x) X1
                   have i₂ := b25e108786 (M.op (σ y) X0)
                   grind)
                | exact superpose b25e108786 b25e332
                | exact resolve b25e332 b25e108786
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e332
              have b25e111794 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ y) X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e200 (σ y) X0 (σ x)
                   have i₂ := b25e108786 (M.op (σ y) X0)
                   grind)
                | exact superpose b25e108786 b25e200
                | exact resolve b25e200 b25e108786
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e111795 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e365 (σ x) X0 (σ y)
                   have i₂ := b25e108786 (M.op (σ y) (M.op (σ x) X0))
                   grind)
                | exact superpose b25e108786 b25e365
                | exact resolve b25e365 b25e108786
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e108786
              have b25e112222 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k x y)) X0) := by
                intro X0
                first
                | (have i₁ := b25e111776 X0
                   have i₂ := b25e4539
                   grind)
                | exact superpose b25e4539 b25e111776
                | exact resolve b25e111776 b25e4539
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e111776
              have b25e114137 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y x)) X0) ∨ y = (M.op x x) := by
                intro X0
                first
                | (have i₁ := b25e112222 X0
                   have i₂ := b25e620 x y
                   grind)
                | exact superpose b25e620 b25e112222
                | (have j1 := b25e620 x y
                   grind)
                | exact resolve b25e112222 b25e620
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e112222
              have b25e114593 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y x)) X0) := by
                intro X0
                first
                | (have j0 := b25e114137 X0
                   grind)
                | (have r₁ := b25e114137 X0
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e114137 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e114137
              have b25e118063 : (σ (M.op (M.op y x) (M.op y x))) = (M.op (σ y) (σ (M.op y x))) := by
                first
                | (have i₁ := b25e65 (M.op y x)
                   have i₂ := b25e114593 (σ (M.op y x))
                   grind)
                | exact superpose b25e114593 b25e65
                | exact resolve b25e65 b25e114593
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e118458 : (M.op (σ y) (σ (M.op y x))) = (σ (M.op x (M.op x (M.op y y)))) := by
                first
                | (have i₁ := b25e118063
                   have i₂ := b25e31265 x y
                   grind)
                | exact superpose b25e31265 b25e118063
                | exact resolve b25e118063 b25e31265
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e118063
              have b25e118564 : (σ (M.op x (M.op x x))) = (M.op (σ y) (σ (M.op y x))) := by
                first
                | (have i₁ := b25e118458
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e118458
                | exact resolve b25e118458 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e118458
              have b25e118881 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) X0)) := by
                intro X0
                first
                | (have i₁ := b25e111777 (M.op (σ x) (M.op (σ y) X0))
                   have i₂ := b25e111777 X0
                   grind)
                | exact superpose b25e111777 b25e111777
                | exact resolve b25e111777 b25e111777
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e118883 : (σ y) = (M.op (σ y) (M.op (σ x) (σ (M.op y y)))) := by
                first
                | (have i₁ := b25e111777 (σ y)
                   have i₂ := b25e65 y
                   grind)
                | exact superpose b25e65 b25e111777
                | exact resolve b25e111777 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e119174 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
                first
                | (have i₁ := b25e118883
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e118883
                | exact resolve b25e118883 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e118883
              have b25e119255 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) := by
                first
                | (have i₁ := b25e119174
                   have i₂ := b25e118881 (σ x)
                   grind)
                | exact superpose b25e118881 b25e119174
                | exact resolve b25e119174 b25e118881
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e119174
              have b25e119315 : (σ y) = (M.op (σ x) (σ (k x y))) := by
                first
                | (have i₁ := b25e119255
                   have i₂ := b25e4539
                   grind)
                | exact superpose b25e4539 b25e119255
                | exact resolve b25e119255 b25e4539
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e119255
              have b25e121600 : (σ y) = (M.op (σ x) (σ (M.op y x))) ∨ y = (M.op x x) := by
                first
                | (have i₁ := b25e119315
                   have i₂ := b25e620 x y
                   grind)
                | exact superpose b25e620 b25e119315
                | (have j1 := b25e620 x y
                   grind)
                | exact resolve b25e119315 b25e620
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e620
              have b25e121771 : (σ y) = (M.op (σ x) (σ (M.op y x))) := by
                first
                | (have r₁ := b25e121600
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e121600 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e121600
              have b25e121948 : ∀ X0 : G, (σ (M.op y x)) = (M.op X0 (M.op (M.op X0 (σ x)) (σ y))) := by
                intro X0
                first
                | (have i₁ := b25e200 (σ x) (σ (M.op y x)) X0
                   have i₂ := b25e121771
                   grind)
                | exact superpose b25e121771 b25e200
                | exact resolve b25e200 b25e121771
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e200 b25e121771
              have b25e122080 : (σ (M.op y x)) = (M.op (σ y) (M.op (σ y) (σ y))) := by
                first
                | (have i₁ := b25e121948 x
                   have i₂ := b25e111793 (σ y) x
                   grind)
                | exact superpose b25e111793 b25e121948
                | exact resolve b25e121948 b25e111793
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e111793 b25e121948
              have b25e122126 : (σ (M.op y x)) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b25e122080
                   have i₂ := b25e65 y
                   grind)
                | exact superpose b25e65 b25e122080
                | exact resolve b25e122080 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e122080
              have b25e122161 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
                first
                | (have i₁ := b25e122126
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e122126
                | exact resolve b25e122126 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e122126
              have b25e124125 : (σ x) = (M.op (σ y) (M.op (σ x) (σ (M.op y x)))) := by
                first
                | (have i₁ := b25e111777 (σ x)
                   have i₂ := b25e122161
                   grind)
                | exact superpose b25e122161 b25e111777
                | exact resolve b25e111777 b25e122161
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e111777
              have b25e124145 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (M.op (σ y) (M.op (σ (M.op y x)) X0)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e184 X0 (σ y) (σ x) X1
                   have i₂ := b25e122161
                   grind)
                | exact superpose b25e122161 b25e184
                | exact resolve b25e184 b25e122161
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e122161
              have b25e124292 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (M.op (σ y) (M.op (σ y) X0)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e124145 X0 X1
                   have i₂ := b25e114593 X0
                   grind)
                | exact superpose b25e114593 b25e124145
                | exact resolve b25e124145 b25e114593
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e114593 b25e124145
              have b25e124300 : (σ x) = (M.op (σ x) (M.op (σ y) (σ (M.op y x)))) := by
                first
                | (have i₁ := b25e124125
                   have i₂ := b25e118881 (σ (M.op y x))
                   grind)
                | exact superpose b25e118881 b25e124125
                | exact resolve b25e124125 b25e118881
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e124125
              have b25e124343 : (σ x) = (M.op (σ x) (σ (M.op x (M.op x x)))) := by
                first
                | (have i₁ := b25e124300
                   have i₂ := b25e118564
                   grind)
                | exact superpose b25e118564 b25e124300
                | exact resolve b25e124300 b25e118564
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e118564 b25e124300
              have b25e127966 : (σ x) = (M.op (σ y) (M.op (σ y) (σ (M.op x x)))) := by
                first
                | (have i₁ := b25e111795 (σ x)
                   have i₂ := b25e65 x
                   grind)
                | exact superpose b25e65 b25e111795
                | exact resolve b25e111795 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e111795
              have b25e130223 : ∀ X0 : G, (M.op (σ (M.op x (M.op x x))) X0) = (M.op (M.op (σ x) (σ x)) X0) := by
                intro X0
                first
                | (have i₁ := b25e36 X0 (σ (M.op x (M.op x x))) (σ x)
                   have i₂ := b25e124343
                   grind)
                | exact superpose b25e124343 b25e36
                | exact resolve b25e36 b25e124343
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e130250 : ∀ X0 X1 : G, (M.op (σ (M.op x (M.op x x))) (M.op X0 X1)) = (M.op (M.op (σ x) X0) (M.op (σ x) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e292 X1 (σ x) (σ (M.op x (M.op x x))) X0
                   have i₂ := b25e124343
                   grind)
                | exact superpose b25e124343 b25e292
                | exact resolve b25e292 b25e124343
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e124343
              have b25e130359 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op X0 X1)) = (M.op (σ (M.op x (M.op x x))) (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e130250 X0 X1
                   have i₂ := b25e13183 x X0 X1
                   grind)
                | exact superpose b25e13183 b25e130250
                | exact resolve b25e130250 b25e13183
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e130250
              have b25e130371 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ (M.op x (M.op x x))) X0) := by
                intro X0
                first
                | (have i₁ := b25e130223 X0
                   have i₂ := b25e65 x
                   grind)
                | exact superpose b25e65 b25e130223
                | exact resolve b25e130223 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e130223
              have b25e136345 : (M.op (σ x) (M.op (σ y) (σ x))) = (M.op (σ y) (σ (M.op x x))) := by
                first
                | (have i₁ := b25e111794 (M.op (σ y) (σ (M.op x x)))
                   have i₂ := b25e127966
                   grind)
                | exact superpose b25e127966 b25e111794
                | exact resolve b25e111794 b25e127966
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e111794 b25e127966
              have b25e136583 : (M.op (σ x) (σ (k x y))) = (M.op (σ y) (σ (M.op x x))) := by
                first
                | (have i₁ := b25e136345
                   have i₂ := b25e4539
                   grind)
                | exact superpose b25e4539 b25e136345
                | exact resolve b25e136345 b25e4539
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4539 b25e136345
              have b25e136669 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
                first
                | (have i₁ := b25e136583
                   have i₂ := b25e119315
                   grind)
                | exact superpose b25e119315 b25e136583
                | exact resolve b25e136583 b25e119315
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e119315 b25e136583
              have b25e137540 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
                intro X0
                first
                | (have i₁ := b25e36 X0 (σ (M.op x x)) (σ y)
                   have i₂ := b25e136669
                   grind)
                | exact superpose b25e136669 b25e36
                | exact resolve b25e36 b25e136669
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e137553 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ y) X0)) X1) = (M.op (M.op X0 (σ (M.op x x))) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e184 X0 (σ y) (σ (M.op x x)) X1
                   have i₂ := b25e136669
                   grind)
                | exact superpose b25e136669 b25e184
                | exact resolve b25e184 b25e136669
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e184
              have b25e137566 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op X0 X1)) = (M.op (M.op (σ y) X0) (M.op (σ y) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e292 X1 (σ y) (σ (M.op x x)) X0
                   have i₂ := b25e136669
                   grind)
                | exact superpose b25e136669 b25e292
                | exact resolve b25e292 b25e136669
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e292
              have b25e137691 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op X0 X1)) = (M.op (σ (M.op y y)) (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e137566 X0 X1
                   have i₂ := b25e13183 y X0 X1
                   grind)
                | exact superpose b25e13183 b25e137566
                | exact resolve b25e137566 b25e13183
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e137566
              have b25e137699 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (M.op X0 (σ (M.op x x))) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e137553 X0 X1
                   have i₂ := b25e124292 X0 X1
                   grind)
                | exact superpose b25e124292 b25e137553
                | exact resolve b25e137553 b25e124292
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e124292 b25e137553
              have b25e137703 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ (M.op x x)) X0) := by
                intro X0
                first
                | (have i₁ := b25e137540 X0
                   have i₂ := b25e65 y
                   grind)
                | exact superpose b25e65 b25e137540
                | exact resolve b25e137540 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e137540
              have b25e137739 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ (M.op x x)) (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e137691 X0 X1
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e137691
                | exact resolve b25e137691 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e137691
              have b25e137750 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x x)) X0) := by
                intro X0
                first
                | (have i₁ := b25e137703 X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e137703
                | exact resolve b25e137703 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e137703
              have b25e138604 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
                first
                | (have i₁ := b25e65 (M.op x x)
                   have i₂ := b25e137750 (σ (M.op x x))
                   grind)
                | exact superpose b25e137750 b25e65
                | exact resolve b25e65 b25e137750
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e139028 : (M.op (σ x) (σ (M.op x x))) = (σ (M.op x (M.op y (M.op x y)))) := by
                first
                | (have i₁ := b25e138604
                   have i₂ := b25e8496 x x
                   grind)
                | exact superpose b25e8496 b25e138604
                | exact resolve b25e138604 b25e8496
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e8496 b25e138604
              have b25e139147 : (σ (M.op y (M.op y x))) = (M.op (σ x) (σ (M.op x x))) := by
                first
                | (have i₁ := b25e139028
                   have i₂ := b25e25053 y
                   grind)
                | exact superpose b25e25053 b25e139028
                | exact resolve b25e139028 b25e25053
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e25053 b25e139028
              have b25e139210 : (σ (M.op x (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
                first
                | (have i₁ := b25e139147
                   have i₂ := b25e1639 x
                   grind)
                | exact superpose b25e1639 b25e139147
                | exact resolve b25e139147 b25e1639
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1639 b25e139147
              have b25e150341 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
                intro X0
                first
                | (have i₁ := b25e325 X0 (σ (M.op X0 X0))
                   have i₂ := b25e65 (M.op X0 X0)
                   grind)
                | exact superpose b25e65 b25e325
                | exact resolve b25e325 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e325
              have b25e150733 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
                intro X0
                first
                | (have i₁ := b25e150341 X0
                   have i₂ := b25e785 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
                   grind)
                | exact superpose b25e785 b25e150341
                | exact resolve b25e150341 b25e785
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e785 b25e150341
              have b25e218807 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ y) (σ X0)) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e3077 (σ X0)
                   have i₂ := b25e16 X0
                   grind)
                | exact superpose b25e16 b25e3077
                | exact resolve b25e3077 b25e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3077
              have b25e218850 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e218807 X0
                   have i₂ := b25e21 y X0
                   grind)
                | exact superpose b25e21 b25e218807
                | (have j0 := b25e218807 X0
                   grind)
                | exact resolve b25e218807 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e218807
              have b25e220971 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op y (M.op x y)) (M.op y (M.op x y))))) := by
                first
                | (have i₁ := b25e150733 (M.op x y)
                   have i₂ := b25e38 (M.op x y)
                   grind)
                | exact superpose b25e38 b25e150733
                | exact resolve b25e150733 b25e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e38 b25e150733
              have b25e221193 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x (M.op (M.op (M.op y (M.op x y)) x) x)))) := by
                first
                | (have i₁ := b25e220971
                   have i₂ := b25e21560 (M.op y (M.op x y)) x
                   grind)
                | exact superpose b25e21560 b25e220971
                | exact resolve b25e220971 b25e21560
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e21560 b25e220971
              have b25e221262 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x (M.op (M.op (M.op x (M.op x y)) y) x)))) := by
                first
                | (have i₁ := b25e221193
                   have i₂ := b25e33353 x y y x x
                   grind)
                | exact superpose b25e33353 b25e221193
                | exact resolve b25e221193 b25e33353
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e33353 b25e221193
              have b25e221321 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y (M.op (M.op (M.op y x) x) x)))) := by
                first
                | (have i₁ := b25e221262
                   have i₂ := b25e45006 x x x y
                   grind)
                | exact superpose b25e45006 b25e221262
                | exact resolve b25e221262 b25e45006
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e45006 b25e221262
              have b25e221365 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op y x) (M.op y x)))) := by
                first
                | (have i₁ := b25e221321
                   have i₂ := b25e2982 (M.op y x) x
                   grind)
                | exact superpose b25e2982 b25e221321
                | exact resolve b25e221321 b25e2982
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2982 b25e221321
              have b25e221393 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x (M.op x (M.op y y))))) := by
                first
                | (have i₁ := b25e221365
                   have i₂ := b25e31265 x y
                   grind)
                | exact superpose b25e31265 b25e221365
                | exact resolve b25e221365 b25e31265
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e31265 b25e221365
              have b25e221412 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x (M.op x x)))) := by
                first
                | (have i₁ := b25e221393
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e221393
                | exact resolve b25e221393 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e221393
              have b25e318540 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e16 (M.op X1 X1)
                   have i₂ := b25e2439 X0 X1
                   grind)
                | (have i₁ := b25e16 X0
                   have i₂ := b25e2439 (σ X0) X1
                   grind)
                | exact superpose b25e2439 b25e16
                | (have j1 := b25e2439 X0 X1
                   grind)
                | exact resolve b25e16 b25e2439
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2439
              have b25e382381 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (σ (M.op y y)) (M.op X0 (σ (M.op x x)))) := by
                intro X0
                first
                | (have i₁ := b25e13183 y X0 (σ (M.op x x))
                   have i₂ := b25e136669
                   grind)
                | exact superpose b25e136669 b25e13183
                | exact resolve b25e13183 b25e136669
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e13183
              have b25e382512 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (σ x) (M.op X0 (σ (M.op x x)))) := by
                intro X0
                first
                | (have i₁ := b25e382381 X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e382381
                | exact resolve b25e382381 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e382381
              have b25e392659 : ∀ X0 : G, (τ X0) = x ∨ (k (σ (M.op y (M.op x x))) X0) = (M.op X0 (σ (M.op y (M.op x x)))) := by
                intro X0
                first
                | (have i₁ := b25e39 x x
                   have i₂ := b25e318540 X0 (M.op y (M.op x x))
                   grind)
                | exact superpose b25e318540 b25e39
                | (have j1 := b25e318540 X0 (M.op y (M.op x x))
                   grind)
                | exact resolve b25e39 b25e318540
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e39 b25e318540
              have b25e392684 : ∀ X0 : G, (k (σ (M.op x (M.op y x))) X0) = (M.op X0 (σ (M.op x (M.op y x)))) ∨ (τ X0) = x := by
                intro X0
                first
                | (have i₁ := b25e392659 X0
                   have i₂ := b25e109 x
                   grind)
                | exact superpose b25e109 b25e392659
                | (have j0 := b25e392659 X0
                   grind)
                | exact resolve b25e392659 b25e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e109 b25e392659
              have b25e392708 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (τ X0) = x := by
                intro X0
                first
                | (have i₁ := b25e392684 X0
                   have i₂ := b25e115
                   grind)
                | exact superpose b25e115 b25e392684
                | (have j0 := b25e392684 X0
                   grind)
                | exact resolve b25e392684 b25e115
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e392684
              have b25e392732 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ (τ (σ X0)) = x := by
                intro X0
                first
                | (have i₁ := b25e21 y X0
                   have i₂ := b25e392708 (σ X0)
                   grind)
                | exact superpose b25e392708 b25e21
                | (have j1 := b25e392708 (σ X0)
                   grind)
                | exact resolve b25e21 b25e392708
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e392708
              have b25e392738 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e392732 X0
                   have i₂ := b25e16 X0
                   grind)
                | exact superpose b25e16 b25e392732
                | (have j0 := b25e392732 X0
                   grind)
                | exact resolve b25e392732 b25e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e392732
              have b25e392792 : ∀ X0 : G, (σ y) = (M.op (σ X0) (M.op (σ (k y X0)) (σ (M.op y y)))) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e992 y (σ X0)
                   have i₂ := b25e392738 X0
                   grind)
                | exact superpose b25e392738 b25e992
                | (have j1 := b25e392738 X0
                   grind)
                | exact resolve b25e992 b25e392738
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e992 b25e392738
              have b25e392943 : ∀ X0 : G, (σ y) = (M.op (σ X0) (M.op (σ (k y X0)) (σ x))) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e392792 X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e392792
                | (have j0 := b25e392792 X0
                   grind)
                | exact resolve b25e392792 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e392792
              have b25e441628 : (M.op (σ x) (M.op (σ y) (σ (M.op x x)))) = (M.op (σ y) (σ (M.op x (M.op x x)))) := by
                first
                | (have i₁ := b25e118881 (σ (M.op x x))
                   have i₂ := b25e139210
                   grind)
                | exact superpose b25e139210 b25e118881
                | exact resolve b25e118881 b25e139210
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e118881 b25e139210
              have b25e441751 : (M.op (σ y) (σ (M.op x (M.op x x)))) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
                first
                | (have i₁ := b25e441628
                   have i₂ := b25e382512 (σ y)
                   grind)
                | exact superpose b25e382512 b25e441628
                | exact resolve b25e441628 b25e382512
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e382512 b25e441628
              have b25e441814 : (M.op (σ (M.op y y)) (σ y)) = (M.op (σ y) (σ (M.op x (M.op x x)))) := by
                first
                | (have i₁ := b25e441751
                   have i₂ := b25e65 y
                   grind)
                | exact superpose b25e65 b25e441751
                | exact resolve b25e441751 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e65 b25e441751
              have b25e441861 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x (M.op x x)))) := by
                first
                | (have i₁ := b25e441814
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e441814
                | exact resolve b25e441814 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e441814
              have b25e497235 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (σ (M.op x (M.op x x))) (σ (M.op x y))) X0) := by
                intro X0
                first
                | (have i₁ := b25e196 (σ (M.op x (M.op x x))) (σ (M.op x y)) X0
                   have i₂ := b25e221412
                   grind)
                | exact superpose b25e221412 b25e196
                | exact resolve b25e196 b25e221412
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e196
              have b25e497239 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x (M.op x x))) (M.op (σ (M.op x y)) X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e365 (σ (M.op x y)) X0 (σ (M.op x (M.op x x)))
                   have i₂ := b25e221412
                   grind)
                | exact superpose b25e221412 b25e365
                | exact resolve b25e365 b25e221412
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e497242 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x x)) (M.op (σ (M.op x y)) X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e497239 X0
                   have i₂ := b25e130359 (σ (M.op x y)) X0
                   grind)
                | exact superpose b25e130359 b25e497239
                | exact resolve b25e497239 b25e130359
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e130359 b25e497239
              have b25e497244 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (σ (M.op x x)) (σ (M.op x y))) X0) := by
                intro X0
                first
                | (have i₁ := b25e497235 X0
                   have i₂ := b25e130371 (σ (M.op x y))
                   grind)
                | exact superpose b25e130371 b25e497235
                | exact resolve b25e497235 b25e130371
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e130371 b25e497235
              have b25e497247 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ (M.op x y)) X0))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e497242 X0
                   have i₂ := b25e137739 (σ (M.op x y)) X0
                   grind)
                | exact superpose b25e137739 b25e497242
                | exact resolve b25e497242 b25e137739
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e137739 b25e497242
              have b25e497249 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (σ x) (σ (M.op x y))) X0) := by
                intro X0
                first
                | (have i₁ := b25e497244 X0
                   have i₂ := b25e137750 (σ (M.op x y))
                   grind)
                | exact superpose b25e137750 b25e497244
                | exact resolve b25e497244 b25e137750
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e137750 b25e497244
              have b25e518948 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (σ (M.op x y)) (σ x)) X0) := by
                intro X0
                first
                | (have i₁ := b25e797 (σ (M.op x y)) (σ (M.op x y)) (σ x) X0
                   have i₂ := b25e497247 (σ x)
                   grind)
                | exact superpose b25e497247 b25e797
                | exact resolve b25e797 b25e497247
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e797 b25e497247
              have b25e545310 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (k y X0)) (σ X0)) (σ y)) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e365 (σ (k y X0)) (σ x) (σ X0)
                   have i₂ := b25e392943 X0
                   grind)
                | exact superpose b25e392943 b25e365
                | (have j1 := b25e392943 X0
                   grind)
                | exact resolve b25e365 b25e392943
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e365 b25e392943
              have b25e560256 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op X0 y)) (σ X0)) (σ y)) ∨ x = X0 ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e545310 X0
                   have i₂ := b25e218850 X0
                   grind)
                | exact superpose b25e218850 b25e545310
                | (have j0 := b25e545310 X0
                   have j1 := b25e218850 X0
                   grind)
                | exact resolve b25e545310 b25e218850
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e218850 b25e545310
              have b25e560299 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op X0 y)) (σ X0)) (σ y)) ∨ x = X0 := by
                intro X0
                first
                | (have j0 := b25e560256 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e560256
              have b25e569302 : (σ x) = (M.op (M.op (σ (M.op (M.op x x) y)) (σ x)) (σ y)) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b25e137699 (σ (M.op (M.op x x) y)) (σ y)
                   have i₂ := b25e560299 (M.op x x)
                   grind)
                | exact superpose b25e560299 b25e137699
                | (have j1 := b25e560299 (M.op x x)
                   grind)
                | exact resolve b25e137699 b25e560299
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e137699 b25e560299
              have b25e569349 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b25e569302
                   have i₂ := b25e1640 y
                   grind)
                | exact superpose b25e1640 b25e569302
                | exact resolve b25e569302 b25e1640
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1640 b25e569302
              have b25e569374 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b25e569349
                   have i₂ := b25e518948 (σ y)
                   grind)
                | exact superpose b25e518948 b25e569349
                | exact resolve b25e569349 b25e518948
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e518948 b25e569349
              have b25e569421 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ (M.op x y))) X0) ∨ x = (M.op x x) := by
                intro X0
                first
                | (have i₁ := b25e36 X0 (σ y) (σ (M.op x y))
                   have i₂ := b25e569374
                   grind)
                | exact superpose b25e569374 b25e36
                | exact resolve b25e36 b25e569374
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e36 b25e569374
              have b25e569433 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x x) := by
                intro X0
                first
                | (have i₁ := b25e569421 X0
                   have i₂ := b25e497249 X0
                   grind)
                | exact superpose b25e497249 b25e569421
                | exact resolve b25e569421 b25e497249
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e497249 b25e569421
              have b25e571418 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x (M.op x x)))) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b25e221412
                   have i₂ := b25e569433 (σ (M.op x (M.op x x)))
                   grind)
                | exact superpose b25e569433 b25e221412
                | exact resolve b25e221412 b25e569433
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e221412 b25e569433
              have b25e571446 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b25e571418
                   have i₂ := b25e441861
                   grind)
                | exact superpose b25e441861 b25e571418
                | exact resolve b25e571418 b25e441861
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e571418
              have b25e571469 : x = (M.op x x) := by
                first
                | (have r₁ := b25e571446
                   have r₂ := b25e22
                   grind)
                | exact resolve b25e571446 b25e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e571446
              have b25e571552 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x x))) := by
                first
                | (have i₁ := b25e441861
                   have i₂ := b25e571469
                   grind)
                | exact superpose b25e571469 b25e441861
                | exact resolve b25e441861 b25e571469
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e441861
              have b25e571644 : (M.op x y) = (M.op x (M.op y x)) := by
                first
                | (have i₁ := b25e68854 x
                   have i₂ := b25e571469
                   grind)
                | exact superpose b25e571469 b25e68854
                | exact resolve b25e68854 b25e571469
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e68854 b25e571469
              have b25e572343 : y = (M.op x y) := by
                first
                | (have i₁ := b25e571644
                   have i₂ := b25e115
                   grind)
                | exact superpose b25e115 b25e571644
                | exact resolve b25e571644 b25e115
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e115 b25e571644
              have b25e572391 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e571552
                   have i₂ := b25e136669
                   grind)
                | exact superpose b25e136669 b25e571552
                | exact resolve b25e571552 b25e136669
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e136669 b25e571552
              have b25e578366 : (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e572391
                   grind)
                | exact superpose b25e572391 b25e22
                | exact resolve b25e22 b25e572391
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e572391
              have b25e578941 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b25e578366
                   have i₂ := b25e572343
                   grind)
                | exact superpose b25e572343 b25e578366
                | exact resolve b25e578366 b25e572343
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e572343 b25e578366
              have b25e578942 : False := by grind
              exact b25e578942
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e28 : x ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e21
                | exact resolve b26e21 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e34 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X1) X2) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 (M.op (M.op (M.op X2 X1) X2) X0) X1 X2
                   have i₂ := b26e15 X0 X2 (M.op X2 X1)
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b26e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e21 X0 X0
                   have i₂ := b26e48 (σ X0)
                   grind)
                | exact superpose b26e48 b26e21
                | exact resolve b26e21 b26e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e50 X0
                   have i₂ := b26e48 X0
                   grind)
                | exact superpose b26e48 b26e50
                | exact resolve b26e50 b26e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e48 b26e50
              have b26e86 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e18 X0 X1
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e18 X0 X0
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e18
                | (have j0 := b26e18 X0 X0
                   have j1 := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e18 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e18 X1 X1
                   have r₂ := b26e20 X1 X1
                   grind)
                | (have r₁ := b26e18 X0 X1
                   have r₂ := b26e20 X0 (M.op X0 X1)
                   grind)
                | exact resolve b26e18 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e86 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e86
              have b26e126 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X0) X0) X2) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e34 X2 X1 X0
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e34 X0 X0 X0
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e34
                | (have j1 := b26e20 X0 X1
                   grind)
                | exact resolve b26e34 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e152 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e126 X0 X1 X2
                   have i₂ := b26e34 X2 X0 X0
                   grind)
                | exact superpose b26e34 b26e126
                | (have j0 := b26e126 X0 X1 X2
                   grind)
                | exact resolve b26e126 b26e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e34 b26e126
              have b26e437 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e90 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e90
              have b26e440 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e437 X0 X1
                   have j1 := b26e152 X0 X1 x
                   grind)
                | (have r₁ := b26e437 x X0
                   have r₂ := b26e152 X0 x x
                   grind)
                | (have r₁ := b26e437 x X1
                   have r₂ := b26e152 x X1 x
                   grind)
                | (have r₁ := b26e437 X0 X1
                   have r₂ := b26e152 X0 (M.op X1 X0) x
                   grind)
                | exact resolve b26e437 b26e152
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e152 b26e437
              have b26e846 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e31 X0 X1
                   have i₂ := b26e440 X1 (τ X0)
                   grind)
                | exact superpose b26e440 b26e31
                | (have j1 := b26e440 X1 (τ X0)
                   grind)
                | exact resolve b26e31 b26e440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e31
              have b26e880 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e55 X1
                   have i₂ := b26e440 (σ X1) X0
                   grind)
                | (have i₁ := b26e55 X0
                   have i₂ := b26e440 X0 (M.op (σ X0) (σ X0))
                   grind)
                | exact superpose b26e440 b26e55
                | (have j1 := b26e440 (σ X1) X0
                   grind)
                | exact resolve b26e55 b26e440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e55 b26e440
              have b26e83690 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (M.op X1 X1)
                   have i₂ := b26e880 X0 X1
                   grind)
                | (have i₁ := b26e16 X0
                   have i₂ := b26e880 (σ X0) X1
                   grind)
                | exact superpose b26e880 b26e16
                | (have j1 := b26e880 X0 X1
                   grind)
                | exact resolve b26e16 b26e880
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e880
              have b26e125484 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e83690 (σ X0) X1
                   grind)
                | exact superpose b26e83690 b26e21
                | (have j1 := b26e83690 (σ X0) X1
                   grind)
                | exact resolve b26e21 b26e83690
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e83690
              have b26e125544 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e125484 X0 X1
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e125484
                | (have j0 := b26e125484 X0 X1
                   grind)
                | exact resolve b26e125484 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e125484
              have b26e155508 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e846 (σ X0) X1
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e846
                | exact resolve b26e846 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e846
              have b26e156464 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e155508 X0 X1
                   have i₂ := b26e21 X1 X0
                   grind)
                | exact superpose b26e21 b26e155508
                | (have j0 := b26e155508 X0 X1
                   grind)
                | exact resolve b26e155508 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e155508
              have b26e161768 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e125544 x y
                   grind)
                | exact superpose b26e125544 b26e22
                | (have j1 := b26e125544 x y
                   grind)
                | exact resolve b26e22 b26e125544
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e125544
              have b26e162147 : x = (M.op y y) := by
                first
                | (have j1 := b26e156464 x y
                   grind)
                | (have r₁ := b26e161768
                   have r₂ := b26e156464 x y
                   grind)
                | exact resolve b26e161768 b26e156464
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e156464 b26e161768
              have b26e162441 : False := by grind
              exact b26e162441
