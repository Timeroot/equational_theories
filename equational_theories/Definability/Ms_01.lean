import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxy_pxx_pxy_Equation3292 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      have b0e78 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e83 : False := by grind
      exact b0e83
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
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
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e31
          have b4e64 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e32 y
               grind)
            | exact superpose b4e32 b4e27
            | (have r₁ := b4e27
               have r₂ := b4e32 y
               grind)
            | exact resolve b4e27 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e32
          have b4e67 : False := by grind
          exact b4e67
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20
            | exact resolve b5e20 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e34 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e27
          have b5e38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e34 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e34
            | exact resolve b5e34 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e39 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e38
          have b5e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X1 (M.op X2 X0)) X2 X3
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X1 X0) X2 X1
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e45 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 (M.op X2 X3))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 X2 (M.op X2 X3)
               have i₂ := b5e13 (M.op X2 X3) X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e61 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X2 (M.op X1 (σ X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X0) X1 X2
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : (M.op y y) ≠ (M.op y y) ∨ x = y ∨ (M.op x x) = (k x y) := by
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
          have b5e67 : x = y ∨ (M.op x x) = (k x y) := by grind
          clear b5e63
          have b5e68 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e67
               have r₂ := b5e21
               grind)
            | exact resolve b5e67 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67
          have b5e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e75 X0 X1
               have i₂ := b5e31 X1
               grind)
            | exact superpose b5e31 b5e75
            | (have j0 := b5e75 X0 X1
               grind)
            | exact resolve b5e75 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75
          have b5e112 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op X0 (M.op X1 (M.op X0 (τ X2))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e39 X2
               have i₂ := b5e13 (τ X2) X0 X1
               grind)
            | exact superpose b5e13 b5e39
            | exact resolve b5e39 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e131 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e44 X1 x X3
               have i₂ := b5e44 X1 x X0
               grind)
            | (have i₁ := b5e44 X0 X0 x
               have i₂ := b5e44 X0 X1 (M.op X0 X0)
               grind)
            | exact superpose b5e44 b5e44
            | exact resolve b5e44 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e146 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op X2 X1)
               have i₂ := b5e44 X1 X2 X0
               grind)
            | (have i₁ := b5e13 X0 X0 X2
               have i₂ := b5e44 X0 X1 X2
               grind)
            | exact superpose b5e44 b5e13
            | exact resolve b5e13 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e342 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op X0 (σ X3)))))) = (σ (M.op X3 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e31 X3
               have i₂ := b5e45 X1 X2 X0 (σ X3)
               grind)
            | exact superpose b5e45 b5e31
            | exact resolve b5e31 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e489 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X2 (σ (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e131 X0 (σ X0) x
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e131
            | exact resolve b5e131 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131
          have b5e685 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e146 X0 X0 X2
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e146
            | exact resolve b5e146 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1061 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op X5 (M.op X4 (σ (M.op X3 (M.op X0 X2)))))) = (σ (M.op X0 (M.op X1 (M.op X2 X2)))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e61 (M.op X3 (M.op X0 X2)) X4 X5
               have i₂ := b5e43 X2 X3 X0 X1
               grind)
            | exact superpose b5e43 b5e61
            | exact resolve b5e61 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e61
          have b5e1157 : ∀ X0 X2 X3 X4 X5 : G, (σ (M.op X2 X2)) = (M.op X4 (M.op X5 (M.op X4 (σ (M.op X3 (M.op X0 X2)))))) := by
            intro X0 X2 X3 X4 X5
            first
            | (have i₁ := b5e1061 X0 x X2 X3 X4 X5
               have i₂ := b5e146 x X2 X0
               grind)
            | exact superpose b5e146 b5e1061
            | exact resolve b5e1061 b5e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1061
          have b5e2073 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (σ (M.op X0 (M.op X1 (M.op X0 (τ (σ X2)))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e31 X2
               have i₂ := b5e112 X0 X1 (σ X2)
               grind)
            | exact superpose b5e112 b5e31
            | exact resolve b5e31 b5e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2085 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (σ (M.op X0 (M.op X1 (M.op X0 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e2073 X0 X1 X2
               have i₂ := b5e14 X2
               grind)
            | exact superpose b5e14 b5e2073
            | exact resolve b5e2073 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2073
          have b5e2165 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e88 x y
               grind)
            | exact superpose b5e88 b5e24
            | (have j1 := b5e88 x y
               grind)
            | exact resolve b5e24 b5e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2175 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X1) (σ X1))) = (M.op (σ (k X0 X1)) (σ (k X0 X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e44 (σ X1) (σ X0) X2
               have i₂ := b5e88 X0 X1
               grind)
            | exact superpose b5e88 b5e44
            | (have j1 := b5e88 X0 X1
               grind)
            | exact resolve b5e44 b5e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e88
          have b5e2244 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X1) (σ X1))) = (σ (M.op (k X0 X1) (k X0 X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e2175 X0 X1 X2
               have i₂ := b5e31 (k X0 X1)
               grind)
            | exact superpose b5e31 b5e2175
            | (have j0 := b5e2175 X0 X1 X2
               grind)
            | exact resolve b5e2175 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2175
          have b5e2248 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e2165
               have r₂ := b5e26
               grind)
            | exact resolve b5e2165 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2165
          have b5e2272 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X1 X1))) = (σ (M.op (k X0 X1) (k X0 X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e2244 X0 X1 X2
               have i₂ := b5e31 X1
               grind)
            | exact superpose b5e31 b5e2244
            | (have j0 := b5e2244 X0 X1 X2
               grind)
            | exact resolve b5e2244 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2244
          have b5e2275 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b5e2248
               have r₂ := b5e23
               grind)
            | exact resolve b5e2248 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2248
          have b5e2287 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e2275
               have i₂ := b5e68
               grind)
            | exact superpose b5e68 b5e2275
            | exact resolve b5e2275 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2275
          have b5e2292 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e2287
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e2287
            | exact resolve b5e2287 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e2287
          have b5e2644 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ (M.op X1 X1))) = (σ (M.op X2 (M.op X3 (M.op X2 (τ (σ (M.op X1 X1))))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e112 X2 X3 (σ (M.op X1 X1))
               have i₂ := b5e489 X1 (σ (M.op X1 X1)) X0
               grind)
            | (have i₁ := b5e112 X2 X3 (σ (M.op X1 X1))
               have i₂ := b5e489 X1 X0 (σ (M.op X1 X1))
               grind)
            | exact superpose b5e489 b5e112
            | exact resolve b5e112 b5e489
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e112 b5e489
          have b5e2681 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ (M.op X1 X1))) = (σ (M.op X2 (M.op X3 (M.op X2 (M.op X1 X1))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e2644 X0 X1 X2 X3
               have i₂ := b5e14 (M.op X1 X1)
               grind)
            | exact superpose b5e14 b5e2644
            | exact resolve b5e2644 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2644
          have b5e2725 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op X1 X1))) = (σ (M.op X2 (M.op X1 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e2681 X0 X1 X2 x
               have i₂ := b5e146 X2 X1 x
               grind)
            | exact superpose b5e146 b5e2681
            | exact resolve b5e2681 b5e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e146 b5e2681
          have b5e4613 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op X0 (σ (M.op (M.op X1 X2) (M.op X1 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e2085 X1 (M.op X1 X2) X2
               have i₂ := b5e2725 X0 (M.op X1 X2) X1
               grind)
            | exact superpose b5e2725 b5e2085
            | exact resolve b5e2085 b5e2725
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2085 b5e2725
          have b5e91567 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (M.op X4 X4)) = (M.op X5 (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op X0 (σ (M.op X3 X4)))))))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e4613 X5 X3 X4
               have i₂ := b5e342 X0 X1 X2 (M.op X3 X4)
               grind)
            | exact superpose b5e342 b5e4613
            | exact resolve b5e4613 b5e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e342 b5e4613
          have b5e91951 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X4 X4)) = (M.op X1 (M.op X2 (M.op X1 (M.op X0 (σ (M.op X3 X4)))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e91567 X0 X1 X2 X3 X4 x
               have i₂ := b5e685 X1 X2 (M.op X0 (σ (M.op X3 X4))) x X0
               grind)
            | exact superpose b5e685 b5e91567
            | exact resolve b5e91567 b5e685
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e685 b5e91567
          have b5e288348 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e2272 x y x
               have i₂ := b5e68
               grind)
            | exact superpose b5e68 b5e2272
            | (have j0 := b5e2272 x y x
               grind)
            | exact resolve b5e2272 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68 b5e2272
          have b5e288682 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e288348 X0
               grind)
            | (have r₁ := b5e288348 X0
               have r₂ := b5e26
               grind)
            | exact resolve b5e288348 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e288348
          have b5e288689 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
            intro X0
            first
            | (have j0 := b5e288682 X0
               grind)
            | (have r₁ := b5e288682 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e288682 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e288682
          have b5e288798 : ∀ X0 X1 X2 : G, (σ (M.op x x)) = (M.op X1 (M.op X2 (M.op X1 (M.op X0 (σ (M.op y y)))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1157 x x (M.op x x) X1 X2
               have i₂ := b5e288689 X0
               grind)
            | exact superpose b5e288689 b5e1157
            | exact resolve b5e1157 b5e288689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1157 b5e288689
          have b5e288865 : (σ (M.op y y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e288798 x x x
               have i₂ := b5e91951 x x x y y
               grind)
            | exact superpose b5e91951 b5e288798
            | exact resolve b5e288798 b5e91951
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91951 b5e288798
          have b5e288936 : False := by grind
          exact b5e288936
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
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e65 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e69 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e65
          have b7e70 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e23
               grind)
            | exact resolve b7e69 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e71 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e70
            | exact resolve b7e70 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e72 : (σ (k x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e71
            | exact resolve b7e71 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e71
          have b7e76 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e14
            | exact resolve b7e14 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e77 : (k x y) = (M.op x x) := by
            first
            | (have i₁ := b7e76
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e76
            | exact resolve b7e76 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e105 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e106 : (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have r₁ := b7e105
               have r₂ := b7e22
               grind)
            | exact resolve b7e105 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e108 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e106
               have r₂ := b7e21
               grind)
            | exact resolve b7e106 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e106
          have b7e158 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b7e13 x x x
               have i₂ := b7e108
               grind)
            | exact superpose b7e108 b7e13
            | exact resolve b7e13 b7e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e159 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e158 x
               have i₂ := b7e13 y x x
               grind)
            | exact superpose b7e13 b7e158
            | exact resolve b7e158 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e158
          have b7e160 : False := by grind
          exact b7e160
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e82 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e82
            | (have j0 := b8e82 X0 X1
               grind)
            | exact resolve b8e82 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e2211 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e94 x y
               grind)
            | exact superpose b8e94 b8e20
            | (have j1 := b8e94 x y
               grind)
            | exact resolve b8e20 b8e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94
          have b8e2298 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e2211
               have r₂ := b8e23
               grind)
            | exact resolve b8e2211 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2211
          have b8e43312 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e2298
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e2298
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e2298
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e2298
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e2298 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2298
          have b8e43313 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
          clear b8e43312
          have b8e43316 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have r₁ := b8e43313
               have r₂ := b8e22
               grind)
            | exact resolve b8e43313 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43313
          have b8e43320 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e43316
               have r₂ := b8e21
               grind)
            | exact resolve b8e43316 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43316
          have b8e43324 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e43320
               grind)
            | exact superpose b8e43320 b8e24
            | exact resolve b8e24 b8e43320
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43320
          have b8e43427 : False := by grind
          exact b8e43427

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation3292 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
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
      have b0e62 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e65 : False := by grind
      exact b0e65
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e41 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 y)) := by
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
          have b5e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X1 (M.op X2 X0)) X2 X3
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X1 X0) X2 X1
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e46 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b5e41 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e41
            | exact resolve b5e41 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e49 : y = (M.op y y) := by
            first
            | (have i₁ := b5e46
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e46
            | exact resolve b5e46 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e64 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e13 y y x
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e13
            | exact resolve b5e13 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e79 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 y
               have i₂ := b5e64 X0
               grind)
            | exact superpose b5e64 b5e13
            | exact resolve b5e13 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e83 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e79 X0
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e79
            | exact resolve b5e79 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e88 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X2 (M.op X1 (σ X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X0) X1 X2
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e125 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X1 (M.op X1 X2)
               have i₂ := b5e44 (M.op X1 X2) X0 X1
               grind)
            | exact superpose b5e44 b5e13
            | exact resolve b5e13 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e597 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (σ X0))) (M.op X1 (M.op X2 (σ X0)))) = (M.op X2 (M.op X3 (σ (M.op X0 X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e43 (σ X0) X1 X2 X3
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e43
            | exact resolve b5e43 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e697 : ∀ X0 X2 X3 : G, (M.op (σ X0) (σ X0)) = (M.op X2 (M.op X3 (σ (M.op X0 X0)))) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e597 X0 x X2 X3
               have i₂ := b5e125 x X2 (σ X0)
               grind)
            | exact superpose b5e125 b5e597
            | exact resolve b5e597 b5e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e125 b5e597
          have b5e751 : ∀ X0 X2 X3 : G, (σ (M.op X0 X0)) = (M.op X2 (M.op X3 (σ (M.op X0 X0)))) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e697 X0 X2 X3
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e697
            | exact resolve b5e697 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e697
          have b5e1717 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e751 y x x
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e751
            | exact resolve b5e751 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e751
          have b5e1803 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b5e88 y X0 x
               have i₂ := b5e1717 x X0
               grind)
            | exact superpose b5e1717 b5e88
            | exact resolve b5e88 b5e1717
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88 b5e1717
          have b5e1856 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e1803 X0
               have i₂ := b5e83 y
               grind)
            | exact superpose b5e83 b5e1803
            | exact resolve b5e1803 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83 b5e1803
          have b5e1966 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1856 (σ x)
               grind)
            | exact superpose b5e1856 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e1856 (σ x)
               grind)
            | exact resolve b5e24 b5e1856
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1856
          have b5e1968 : False := by grind
          exact b5e1968
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
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e47 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e49 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e47
          have b7e50 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e49
               have r₂ := b7e23
               grind)
            | exact resolve b7e49 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e51 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e50
            | exact resolve b7e50 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e51
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e51 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e62 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e26
               grind)
            | exact resolve b7e61 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e61
          have b7e63 : x = y := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e22
               grind)
            | exact resolve b7e62 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e64 : False := by grind
          exact b7e64
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b8e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e597 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e58 x y
               grind)
            | exact superpose b8e58 b8e20
            | (have j1 := b8e58 x y
               grind)
            | exact resolve b8e20 b8e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e614 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e597
               have r₂ := b8e24
               grind)
            | exact resolve b8e597 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e597
          have b8e622 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e614
               have r₂ := b8e23
               grind)
            | exact resolve b8e614 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e614
          have b8e625 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e622
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e622
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e622
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e622
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e622 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e622
          have b8e626 : y = (M.op x y) ∨ x = y := by grind
          clear b8e625
          have b8e627 : x = y := by
            first
            | (have r₁ := b8e626
               have r₂ := b8e22
               grind)
            | exact resolve b8e626 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e626
          have b8e628 : False := by grind
          exact b8e628

/-- `Equation3495`: `x ◇ x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pyx_Equation3495 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3495 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y y) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e46 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 y
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
      have b0e48 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 (σ y)
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
      have b0e243 : (M.op x y) = (k x y) := by
        first
        | (have j0 := b0e46 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e1455 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b0e48 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e1457 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e1455
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e1455
        | exact resolve b0e1455 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1455
      have b0e1473 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e1457
           have i₂ := b0e243
           grind)
        | exact superpose b0e243 b0e1457
        | exact resolve b0e1457 b0e243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e243 b0e1457
      have b0e1481 : False := by grind
      exact b0e1481
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e56 (σ X0)
             grind)
          | exact superpose b2e56 b2e18
          | exact resolve b2e18 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e58 X0
             have i₂ := b2e56 X0
             grind)
          | exact superpose b2e56 b2e58
          | exact resolve b2e58 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56 b2e58
        have b2e145 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e65 y
             grind)
          | exact superpose b2e65 b2e21
          | exact resolve b2e21 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e153 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e145
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e145
          | exact resolve b2e145 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e145
        have b2e154 : False := by grind
        exact b2e154
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
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e56 (σ X0)
             grind)
          | exact superpose b6e56 b6e18
          | exact resolve b6e18 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e58 X0
             have i₂ := b6e56 X0
             grind)
          | exact superpose b6e56 b6e58
          | exact resolve b6e58 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56 b6e58
        have b6e166 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e65 y
             grind)
          | exact superpose b6e65 b6e22
          | exact resolve b6e22 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e176 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e166
             have i₂ := b6e65 x
             grind)
          | exact superpose b6e65 b6e166
          | exact resolve b6e166 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65 b6e166
        have b6e241 : (M.op y y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (M.op y y)
             have i₂ := b6e176
             grind)
          | exact superpose b6e176 b6e13
          | exact resolve b6e13 b6e176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e176
        have b6e242 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b6e241
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e241
          | exact resolve b6e241 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e241
        have b6e248 : False := by grind
        exact b6e248
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
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
               have i₂ := b8e47 (σ X0)
               grind)
            | exact superpose b8e47 b8e19
            | exact resolve b8e19 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e49 X0
               have i₂ := b8e47 X0
               grind)
            | exact superpose b8e47 b8e49
            | exact resolve b8e49 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47 b8e49
          have b8e65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e74 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ y = X0 := by
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
          have b8e84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e65 X0 X1
               have i₂ := b8e54 X1
               grind)
            | exact superpose b8e54 b8e65
            | (have j0 := b8e65 X0 X1
               grind)
            | exact resolve b8e65 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e84 X0 X1
               have i₂ := b8e54 X0
               grind)
            | exact superpose b8e54 b8e84
            | (have j0 := b8e84 X0 X1
               grind)
            | exact resolve b8e84 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e221 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e54 y
               grind)
            | exact superpose b8e54 b8e23
            | exact resolve b8e23 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e232 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e221
               have i₂ := b8e54 x
               grind)
            | exact superpose b8e54 b8e221
            | exact resolve b8e221 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54 b8e221
          have b8e342 : (M.op x y) = (k y x) ∨ x = y := by
            first
            | (have j0 := b8e74 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e343 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e342
               have r₂ := b8e22
               grind)
            | exact resolve b8e342 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e342
          have b8e3773 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e86 x y
               grind)
            | exact superpose b8e86 b8e20
            | (have j1 := b8e86 x y
               grind)
            | exact resolve b8e20 b8e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e3846 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e3773
               have r₂ := b8e232
               grind)
            | exact resolve b8e3773 b8e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e232 b8e3773
          have b8e3884 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e3846
               have r₂ := b8e24
               grind)
            | exact resolve b8e3846 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3846
          have b8e3903 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e3884
               have i₂ := b8e343
               grind)
            | exact superpose b8e343 b8e3884
            | exact resolve b8e3884 b8e343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e343 b8e3884
          have b8e3904 : False := by grind
          exact b8e3904

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_x_y_pxy_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = y := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : ∀ X0 : G, (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 X0 (M.op X0 x)
           have i₂ := b0e11 X0 X0 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : (σ y) ≠ (σ (M.op y y)) := by grind
      have b0e35 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e32
           have i₂ := b0e30 y
           grind)
        | exact superpose b0e30 b0e32
        | exact resolve b0e32 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30 b0e32
      have b0e36 : False := by grind
      exact b0e36
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
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
          have b5e40 : ∀ X0 : G, (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 X0 (M.op X0 x)
               have i₂ := b5e13 X0 X0 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e47 : x = y ∨ y = (k x y) := by grind
          clear b5e44
          have b5e48 : y = (k x y) := by
            first
            | (have r₁ := b5e47
               have r₂ := b5e21
               grind)
            | exact resolve b5e47 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e91 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op X2 (σ (k X0 X1))))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X0) X2 (σ X1)
               have i₂ := b5e51 X0 X1
               grind)
            | exact superpose b5e51 b5e13
            | (have j1 := b5e51 X0 X1
               grind)
            | exact resolve b5e13 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e775 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e91 x y X0
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e91
            | (have j0 := b5e91 x y x
               grind)
            | exact resolve b5e91 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91
          have b5e802 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ y)))) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e775 X0
               grind)
            | (have r₁ := b5e775 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e775 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e775
          have b5e808 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ y)))) := by
            intro X0
            first
            | (have j0 := b5e802 X0
               grind)
            | (have r₁ := b5e802 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e802 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e802
          have b5e815 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b5e808 (σ y)
               have i₂ := b5e40 (σ y)
               grind)
            | exact superpose b5e40 b5e808
            | exact resolve b5e808 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e808
          have b5e877 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e815
               have i₂ := b5e51 x y
               grind)
            | exact superpose b5e51 b5e815
            | (have j1 := b5e51 x y
               grind)
            | exact resolve b5e815 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e815
          have b5e896 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e877
               have r₂ := b5e24
               grind)
            | exact resolve b5e877 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e877
          have b5e898 : (σ x) = (M.op (σ x) (σ (k x y))) := by
            first
            | (have r₁ := b5e896
               have r₂ := b5e23
               grind)
            | exact resolve b5e896 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e896
          have b5e899 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e898
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e898
            | exact resolve b5e898 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e898
          have b5e900 : False := by grind
          exact b5e900
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e34 : ∀ X0 : G, (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 X0 (M.op X0 x)
               have i₂ := b7e13 X0 X0 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (M.op X0 X1) X1
               have i₂ := b7e34 (M.op X0 X1)
               grind)
            | exact superpose b7e34 b7e13
            | exact resolve b7e13 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e38 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e41 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e38
          have b7e42 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e41
               have r₂ := b7e23
               grind)
            | exact resolve b7e41 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e43 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e42
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e42
            | exact resolve b7e42 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e46 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e43
               grind)
            | exact superpose b7e43 b7e14
            | exact resolve b7e14 b7e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e47 : y = (k x y) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e46
            | exact resolve b7e46 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e56 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e57 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e22
               grind)
            | exact resolve b7e56 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e59 : y = (M.op x y) := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e21
               grind)
            | exact resolve b7e57 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e108 : x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b7e37 x y
               have i₂ := b7e59
               grind)
            | exact superpose b7e59 b7e37
            | exact resolve b7e37 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e119 : x = (M.op x y) := by
            first
            | (have i₁ := b7e108
               have i₂ := b7e59
               grind)
            | exact superpose b7e59 b7e108
            | exact resolve b7e108 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59 b7e108
          have b7e125 : False := by grind
          exact b7e125
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
          have b8e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e92 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e101 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e92
               have r₂ := b8e24
               grind)
            | exact resolve b8e92 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92
          have b8e105 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e101
               have r₂ := b8e23
               grind)
            | exact resolve b8e101 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e101
          have b8e106 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e105
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e105
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e105
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e105
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e105 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e107 : x = (M.op x y) ∨ x = y := by grind
          clear b8e106
          have b8e108 : x = y := by
            first
            | (have r₁ := b8e107
               have r₂ := b8e22
               grind)
            | exact resolve b8e107 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107
          have b8e109 : False := by grind
          exact b8e109

/-- `Equation4364`: `x ◇ (y ◇ z) = y ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation4364 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4364 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4364.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
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
      have b0e63 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e66 : False := by grind
      exact b0e66
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b5e54 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e58 : x = y ∨ y = (k x y) := by grind
          clear b5e54
          have b5e59 : y = (k x y) := by
            first
            | (have r₁ := b5e58
               have r₂ := b5e21
               grind)
            | exact resolve b5e58 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e1100 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e84996 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1100 x y
               have i₂ := b5e59
               grind)
            | exact superpose b5e59 b5e1100
            | (have j0 := b5e1100 x y
               grind)
            | exact resolve b5e1100 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e1100
          have b5e84999 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e84996
          have b5e85001 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e84999
               have r₂ := b5e24
               grind)
            | exact resolve b5e84999 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84999
          have b5e85003 : False := by grind
          exact b5e85003
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
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e49 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e52 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e49
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
          have b7e64 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e54
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e54
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e54 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e65 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e26
               grind)
            | exact resolve b7e64 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e64
          have b7e66 : x = y := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e22
               grind)
            | exact resolve b7e65 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e67 : False := by grind
          exact b7e67
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b8e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e929 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e60 x y
               grind)
            | exact superpose b8e60 b8e20
            | (have j1 := b8e60 x y
               grind)
            | exact resolve b8e20 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e952 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e929
               have r₂ := b8e24
               grind)
            | exact resolve b8e929 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e929
          have b8e958 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e952
               have r₂ := b8e23
               grind)
            | exact resolve b8e952 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e952
          have b8e961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e958
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e958
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e958
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e958
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e958 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e958
          have b8e962 : y = (M.op x y) ∨ x = y := by grind
          clear b8e961
          have b8e963 : x = y := by
            first
            | (have r₁ := b8e962
               have r₂ := b8e22
               grind)
            | exact resolve b8e962 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e962
          have b8e964 : False := by grind
          exact b8e964

/-- `Equation4407`: `x ◇ (x ◇ y) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pxy_Equation4407 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4407 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4407.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X0 X3
           have i₂ := b0e11 X1 X0 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) (σ x) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
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
      have b0e48 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 y X1
           have i₂ := b0e42 X0
           grind)
        | exact superpose b0e42 b0e11
        | exact resolve b0e11 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b0e48 X0 x
           have i₂ := b0e11 y x x
           grind)
        | exact superpose b0e11 b0e48
        | exact resolve b0e48 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e50 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e49 X0
           have i₂ := b0e42 (M.op y x)
           grind)
        | exact superpose b0e42 b0e49
        | exact resolve b0e49 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e49
      have b0e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e16 (σ X0) (σ X1)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e81 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op (M.op X1 X0) y)
           have i₂ := b0e50 (M.op X1 X0)
           grind)
        | exact superpose b0e50 b0e11
        | exact resolve b0e11 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e112 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op x y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e81 X0 X1
           grind)
        | exact superpose b0e81 b0e11
        | exact resolve b0e11 b0e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81
      have b0e130 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e18
        | exact resolve b0e18 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e252 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2
        grind
      clear b0e37
      have b0e265 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op x y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e252 X0 X1 x
           have i₂ := b0e112 X1 X0 x
           grind)
        | exact superpose b0e112 b0e252
        | exact resolve b0e252 b0e112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e252
      have b0e467 : (M.op x y) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e130 (M.op (σ y) y)
           have i₂ := b0e50 (σ y)
           grind)
        | exact superpose b0e50 b0e130
        | exact resolve b0e130 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e130
      have b0e3088 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e63 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63
      have b0e3089 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e3088 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3088
      have b0e4274 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e3089 (M.op x y)
           have i₂ := b0e265 x y
           grind)
        | exact superpose b0e265 b0e3089
        | (have j0 := b0e3089 (M.op x y)
           grind)
        | exact resolve b0e3089 b0e265
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e265 b0e3089
      have b0e4285 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
      clear b0e4274
      have b0e6619 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ (M.op x y)) (σ (M.op x y)) x
           have i₂ := b0e4285
           grind)
        | exact superpose b0e4285 b0e11
        | exact resolve b0e11 b0e4285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e6636 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op x y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e112 (σ (M.op x y)) (σ (M.op x y)) X0
           have i₂ := b0e4285
           grind)
        | exact superpose b0e4285 b0e112
        | exact resolve b0e112 b0e4285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e112
      have b0e6653 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e6619 X0
           have i₂ := b0e4285
           grind)
        | exact superpose b0e4285 b0e6619
        | exact resolve b0e6619 b0e4285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4285 b0e6619
      have b0e6668 : (M.op x y) = (σ (M.op x y)) := by
        first
        | (have i₁ := b0e6653 x
           have i₂ := b0e6636 x
           grind)
        | exact superpose b0e6636 b0e6653
        | exact resolve b0e6653 b0e6636
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6636 b0e6653
      have b0e6676 : False := by grind
      exact b0e6676
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X1 X0 X3
             have i₂ := b1e12 X1 X0 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X1 X0) X1 X3
             have i₂ := b1e12 X1 X0 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e12 x x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e33 X0 X1 X2 X3
             have i₂ := b1e12 X0 X1 (M.op (M.op X1 X0) X1)
             grind)
          | exact superpose b1e12 b1e33
          | exact resolve b1e33 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e42 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 y X1
             have i₂ := b1e36 X0
             grind)
          | exact superpose b1e36 b1e12
          | exact resolve b1e12 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b1e42 X0 x
             have i₂ := b1e12 y x x
             grind)
          | exact superpose b1e12 b1e42
          | exact resolve b1e42 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e44 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e43 X0
             have i₂ := b1e36 (M.op y x)
             grind)
          | exact superpose b1e36 b1e43
          | exact resolve b1e43 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e75 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X0) X1) = (M.op X0 (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (M.op X0 y) X1
             have i₂ := b1e44 X0
             grind)
          | exact superpose b1e44 b1e12
          | exact resolve b1e12 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e77 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b1e75 X0 x
             have i₂ := b1e39 X0 y X0 x
             grind)
          | exact superpose b1e39 b1e75
          | exact resolve b1e75 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e75
        have b1e83 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b1e77 X0
             have i₂ := b1e44 X0
             grind)
          | exact superpose b1e44 b1e77
          | exact resolve b1e77 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e77
        have b1e163 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e31 (σ y) (σ x) x x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e31
          | exact resolve b1e31 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e248 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e22
             have i₂ := b1e163 (σ x) X0
             grind)
          | (have i₁ := b1e22
             have i₂ := b1e163 X0 (σ x)
             grind)
          | exact superpose b1e163 b1e22
          | exact resolve b1e22 b1e163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e163
        have b1e324 : (σ y) = (k (σ y) (σ y)) := by grind
        have b1e333 : (M.op x y) = (σ y) := by
          first
          | (have i₁ := b1e83 (σ y)
             have i₂ := b1e248 (M.op x y)
             grind)
          | exact superpose b1e248 b1e83
          | exact resolve b1e83 b1e248
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e248
        have b1e339 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e324
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e324
          | exact resolve b1e324 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e324
        have b1e718 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e339
             grind)
          | exact superpose b1e339 b1e13
          | exact resolve b1e13 b1e339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e339
        have b1e720 : y = (k y y) := by
          first
          | (have i₁ := b1e718
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e718
          | exact resolve b1e718 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e718
        have b1e943 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e720
             grind)
          | exact superpose b1e720 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e720
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e720
        have b1e944 : y = (M.op y y) := by grind
        clear b1e943
        have b1e946 : y = (M.op x y) := by
          first
          | (have i₁ := b1e944
             have i₂ := b1e36 y
             grind)
          | exact superpose b1e36 b1e944
          | exact resolve b1e944 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e944
        have b1e1311 : y = (σ y) := by
          first
          | (have i₁ := b1e333
             have i₂ := b1e946
             grind)
          | exact superpose b1e946 b1e333
          | exact resolve b1e333 b1e946
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1312 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e83 X0
             have i₂ := b1e946
             grind)
          | exact superpose b1e946 b1e83
          | exact resolve b1e83 b1e946
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e83 b1e946
        have b1e1761 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e1311
             grind)
          | exact superpose b1e1311 b1e19
          | exact resolve b1e19 b1e1311
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1774 : y ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e1761
             have i₂ := b1e1312 (σ x)
             grind)
          | exact superpose b1e1312 b1e1761
          | exact resolve b1e1761 b1e1312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1312 b1e1761
        have b1e1776 : y ≠ (σ (σ y)) := by
          first
          | (have i₁ := b1e1774
             have i₂ := b1e333
             grind)
          | exact superpose b1e333 b1e1774
          | exact resolve b1e1774 b1e333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e333 b1e1774
        have b1e1777 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e1776
             have i₂ := b1e1311
             grind)
          | exact superpose b1e1311 b1e1776
          | exact resolve b1e1776 b1e1311
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1776
        have b1e1778 : False := by grind
        exact b1e1778
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
        have b2e32 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e12 x x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X1 X0) X1 X3
             have i₂ := b2e12 X1 X0 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e33 X0 X1 X2 X3
             have i₂ := b2e12 X0 X1 (M.op (M.op X1 X0) X1)
             grind)
          | exact superpose b2e12 b2e33
          | exact resolve b2e33 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e40 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 y X1
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e12
          | exact resolve b2e12 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b2e40 X0 x
             have i₂ := b2e12 y x x
             grind)
          | exact superpose b2e12 b2e40
          | exact resolve b2e40 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e42 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e41 X0
             have i₂ := b2e32 (M.op y x)
             grind)
          | exact superpose b2e32 b2e41
          | exact resolve b2e41 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e41
        have b2e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e69 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X0) X1) = (M.op X0 (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 (M.op X0 y) X1
             have i₂ := b2e42 X0
             grind)
          | exact superpose b2e42 b2e12
          | exact resolve b2e12 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e70 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 (M.op (M.op X1 X0) y)
             have i₂ := b2e42 (M.op X1 X0)
             grind)
          | exact superpose b2e42 b2e12
          | exact resolve b2e12 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e71 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e69 X0 x
             have i₂ := b2e37 X0 y X0 x
             grind)
          | exact superpose b2e37 b2e69
          | exact resolve b2e69 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e69
        have b2e77 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e71 X0
             have i₂ := b2e42 X0
             grind)
          | exact superpose b2e42 b2e71
          | exact resolve b2e71 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e71
        have b2e98 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op x y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e70 X0 X1
             grind)
          | exact superpose b2e70 b2e12
          | exact resolve b2e12 b2e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e117 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        clear b2e26
        have b2e689 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e117
        have b2e702 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e689 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e689
          | exact resolve b2e689 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e689
        have b2e1712 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e61 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e1713 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1712
             have r₂ := b2e22
             grind)
          | exact resolve b2e1712 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1712
        have b2e1714 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1713
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1713
          | exact resolve b2e1713 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1713
        have b2e1715 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1714
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1714
          | exact resolve b2e1714 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1714
        have b2e1734 : ∀ X0 : G, (M.op x y) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e98 (σ y) (σ x) X0
             have i₂ := b2e1715
             grind)
          | exact superpose b2e1715 b2e98
          | exact resolve b2e98 b2e1715
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98
        have b2e2028 : (M.op x y) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1734 (σ x)
             grind)
          | exact superpose b2e1734 b2e21
          | exact resolve b2e21 b2e1734
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2029 : (M.op x y) = (σ x) := by
          first
          | (have i₁ := b2e1715
             have i₂ := b2e1734 (σ y)
             grind)
          | exact superpose b2e1734 b2e1715
          | exact resolve b2e1715 b2e1734
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1715 b2e1734
        have b2e2078 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e2028
             have i₂ := b2e2029
             grind)
          | exact superpose b2e2029 b2e2028
          | exact resolve b2e2028 b2e2029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2028
        have b2e3050 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e77 X0
             have i₂ := b2e2029
             grind)
          | exact superpose b2e2029 b2e77
          | exact resolve b2e77 b2e2029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77 b2e2029
        have b2e3316 : x = (k x (τ (σ x))) := by
          first
          | (have i₁ := b2e702 x
             have i₂ := b2e3050 (σ x)
             grind)
          | exact superpose b2e3050 b2e702
          | exact resolve b2e702 b2e3050
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e702 b2e3050
        have b2e3323 : x = (k x x) := by
          first
          | (have i₁ := b2e3316
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e3316
          | exact resolve b2e3316 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3316
        have b2e3600 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e3323
             grind)
          | exact superpose b2e3323 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e3323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3323
        have b2e3601 : x = (M.op x x) := by grind
        clear b2e3600
        have b2e3617 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e3601
             grind)
          | exact superpose b2e3601 b2e20
          | exact resolve b2e20 b2e3601
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3601
        have b2e3719 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e2078
             have i₂ := b2e3617
             grind)
          | exact superpose b2e3617 b2e2078
          | exact resolve b2e2078 b2e3617
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2078 b2e3617
        have b2e3721 : False := by grind
        exact b2e3721
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
        have b3e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 (τ X0) X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e18
          | exact resolve b3e18 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X1 X0 X3
             have i₂ := b3e12 X1 X0 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 (M.op X1 X0) X1 X3
             have i₂ := b3e12 X1 X0 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e12 x y X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e45 X0 X1 X2 X3
             have i₂ := b3e12 X0 X1 (M.op (M.op X1 X0) X1)
             grind)
          | exact superpose b3e12 b3e45
          | exact resolve b3e45 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e53 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e48 X1
             have i₂ := b3e48 X0
             grind)
          | exact superpose b3e48 b3e48
          | exact resolve b3e48 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e85 : ∀ X0 X1 : G, y ≠ (M.op y X0) ∨ y = (M.op X1 X1) ∨ (k X1 y) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X1 y
             have i₂ := b3e53 X1 X0
             grind)
          | (have i₁ := b3e16 X1 y
             have i₂ := b3e53 X0 X1
             grind)
          | exact superpose b3e53 b3e16
          | (have j0 := b3e16 X1 y
             grind)
          | exact resolve b3e16 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e86 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 y)) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 y X2
             have i₂ := b3e53 X1 X0
             grind)
          | (have i₁ := b3e12 X1 y X2
             have i₂ := b3e53 X0 X1
             grind)
          | exact superpose b3e53 b3e12
          | exact resolve b3e12 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e87 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e21
             have i₂ := b3e53 x X0
             grind)
          | (have i₁ := b3e21
             have i₂ := b3e53 X0 x
             grind)
          | exact superpose b3e53 b3e21
          | exact resolve b3e21 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e88 : ∀ X1 X2 : G, (M.op y X2) = (M.op X1 (M.op X1 y)) := by
          intro X1 X2
          first
          | (have i₁ := b3e86 x X1 X2
             have i₂ := b3e87 x
             grind)
          | exact superpose b3e87 b3e86
          | exact resolve b3e86 b3e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86
        have b3e89 : ∀ X1 : G, y = (M.op X1 X1) ∨ (k X1 y) = X1 := by
          intro X1
          first
          | (have j0 := b3e85 x X1
             grind)
          | (have r₁ := b3e85 x X1
             have r₂ := b3e87 x
             grind)
          | exact resolve b3e85 b3e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e94 : ∀ X1 : G, y = (M.op X1 (M.op X1 y)) := by
          intro X1
          first
          | (have i₁ := b3e88 X1 x
             have i₂ := b3e87 x
             grind)
          | exact superpose b3e87 b3e88
          | exact resolve b3e88 b3e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87 b3e88
        have b3e109 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) ∨ (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2 (M.op X2 X1)
             have i₂ := b3e17 (M.op X2 X1) X0
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 X0 (M.op (M.op X1 X0) X2)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 (M.op X2 X1) X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e171 : y = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e47 (M.op (σ y) y)
             have i₂ := b3e94 (σ y)
             grind)
          | exact superpose b3e94 b3e47
          | exact resolve b3e47 b3e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e174 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (M.op X0 y) X1
             have i₂ := b3e94 X0
             grind)
          | exact superpose b3e94 b3e12
          | exact resolve b3e12 b3e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e175 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 (M.op (M.op X1 X0) y)
             have i₂ := b3e94 (M.op X1 X0)
             grind)
          | exact superpose b3e94 b3e12
          | exact resolve b3e12 b3e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e176 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e174 X0 x
             have i₂ := b3e51 X0 y X0 x
             grind)
          | exact superpose b3e51 b3e174
          | exact resolve b3e174 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51 b3e174
        have b3e182 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e176 X0
             have i₂ := b3e94 X0
             grind)
          | exact superpose b3e94 b3e176
          | exact resolve b3e176 b3e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e176
        have b3e228 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e94 (M.op X0 X1)
             have i₂ := b3e43 X0 X1 (M.op (M.op X0 X1) y) X2
             grind)
          | (have i₁ := b3e94 (M.op X0 X1)
             have i₂ := b3e43 X0 X1 X2 (M.op (M.op X0 X1) y)
             grind)
          | exact superpose b3e43 b3e94
          | exact resolve b3e94 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e94
        have b3e423 : y ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e171
             grind)
          | exact superpose b3e171 b3e19
          | exact resolve b3e19 b3e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e433 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e423
             have i₂ := b3e182 x
             grind)
          | exact superpose b3e182 b3e423
          | exact resolve b3e423 b3e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e182 b3e423
        have b3e3996 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
          intro X0
          grind
        clear b3e89
        have b3e4048 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e3996 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3996
        have b3e4102 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e28 X0 y
             have i₂ := b3e4048 (τ X0)
             grind)
          | exact superpose b3e4048 b3e28
          | exact resolve b3e28 b3e4048
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e4048
        have b3e4103 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e4102 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e4102
          | exact resolve b3e4102 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4102
        have b3e4314 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ (σ y) = (M.op X1 (M.op X1 X0)) ∨ (σ y) = (M.op (σ y) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e109 (σ y) X1 X0
             have i₂ := b3e4103 (M.op X0 X1)
             grind)
          | exact superpose b3e4103 b3e109
          | (have j0 := b3e109 (σ y) X1 X0
             grind)
          | exact resolve b3e109 b3e4103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e109 b3e4103
        have b3e4320 : ∀ X0 X1 : G, (M.op X0 X1) = y ∨ (σ y) = (M.op X1 (M.op X1 X0)) ∨ (σ y) = (M.op (σ y) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e4314 X0 X1
             have i₂ := b3e228 X0 X1 (σ y)
             grind)
          | exact superpose b3e228 b3e4314
          | (have j0 := b3e4314 X0 X1
             grind)
          | exact resolve b3e4314 b3e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e228 b3e4314
        have b3e4332 : ∀ X0 X1 : G, y = (σ y) ∨ (M.op X0 X1) = y ∨ (σ y) = (M.op (σ y) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e4320 X0 X1
             have i₂ := b3e175 X1 X0
             grind)
          | exact superpose b3e175 b3e4320
          | (have j0 := b3e4320 X0 X1
             grind)
          | exact resolve b3e4320 b3e175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e175 b3e4320
        have b3e4342 : ∀ X0 X1 : G, (M.op X0 X1) = y ∨ (σ y) = (M.op (σ y) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e4332 X0 X1
             grind)
          | (have r₁ := b3e4332 X0 X1
             have r₂ := b3e433
             grind)
          | exact resolve b3e4332 b3e433
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4332
        have b3e4346 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X1) = y := by
          intro X0 X1
          first
          | (have i₁ := b3e4342 X0 X1
             have i₂ := b3e47 (M.op X0 X1)
             grind)
          | exact superpose b3e47 b3e4342
          | (have j0 := b3e4342 X0 X1
             grind)
          | exact resolve b3e4342 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e4342
        have b3e4348 : ∀ X0 X1 : G, y = (σ y) ∨ (M.op X0 X1) = y := by
          intro X0 X1
          first
          | (have i₁ := b3e4346 X0 X1
             have i₂ := b3e171
             grind)
          | exact superpose b3e171 b3e4346
          | (have j0 := b3e4346 X0 X1
             grind)
          | exact resolve b3e4346 b3e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171 b3e4346
        have b3e4350 : ∀ X0 X1 : G, (M.op X0 X1) = y := by
          intro X0 X1
          first
          | (have j0 := b3e4348 X0 X1
             grind)
          | (have r₁ := b3e4348 X0 X1
             have r₂ := b3e433
             grind)
          | exact resolve b3e4348 b3e433
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e433 b3e4348
        have b3e4663 : y ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e4350 x x
             grind)
          | exact superpose b3e4350 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e4350 x x
             grind)
          | exact resolve b3e20 b3e4350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4350
        have b3e4669 : False := by grind
        exact b3e4669
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X0 X3
               have i₂ := b4e13 X1 X0 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op y X0) := by
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
          have b4e41 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X1
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e36
            | exact resolve b4e36 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e90 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 y)) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 y X2
               have i₂ := b4e41 X1 X0
               grind)
            | (have i₁ := b4e13 X1 y X2
               have i₂ := b4e41 X0 X1
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e91 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e22
               have i₂ := b4e41 x X0
               grind)
            | (have i₁ := b4e22
               have i₂ := b4e41 X0 x
               grind)
            | exact superpose b4e41 b4e22
            | exact resolve b4e22 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e92 : ∀ X1 X2 : G, (M.op y X2) = (M.op X1 (M.op X1 y)) := by
            intro X1 X2
            first
            | (have i₁ := b4e90 x X1 X2
               have i₂ := b4e91 x
               grind)
            | exact superpose b4e91 b4e90
            | exact resolve b4e90 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e98 : ∀ X1 : G, y = (M.op X1 (M.op X1 y)) := by
            intro X1
            first
            | (have i₁ := b4e92 X1 x
               have i₂ := b4e91 x
               grind)
            | exact superpose b4e91 b4e92
            | exact resolve b4e92 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91 b4e92
          have b4e189 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op X0 y) X1
               have i₂ := b4e98 X0
               grind)
            | exact superpose b4e98 b4e13
            | exact resolve b4e13 b4e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e191 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e31 X0 X1 (M.op (M.op X0 X1) y) X2
               have i₂ := b4e98 (M.op X0 X1)
               grind)
            | exact superpose b4e98 b4e31
            | exact resolve b4e31 b4e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e98
          have b4e193 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e189 X0 x
               have i₂ := b4e191 (M.op X0 y) X0 x
               grind)
            | exact superpose b4e191 b4e189
            | exact resolve b4e189 b4e191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e189
          have b4e250 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) (σ x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ x) (σ y) X1
               have i₂ := b4e35 X0
               grind)
            | exact superpose b4e35 b4e13
            | exact resolve b4e13 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e267 : ∀ X0 : G, y = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e250 X0 x
               have i₂ := b4e191 (σ y) (σ x) x
               grind)
            | exact superpose b4e191 b4e250
            | exact resolve b4e250 b4e191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191 b4e250
          have b4e287 : y = (σ y) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e267 (σ x)
               grind)
            | exact superpose b4e267 b4e24
            | exact resolve b4e24 b4e267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e267
          have b4e469 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e287
               grind)
            | exact superpose b4e287 b4e20
            | exact resolve b4e20 b4e287
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e474 : y ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e469
               have i₂ := b4e193 (σ x)
               grind)
            | exact superpose b4e193 b4e469
            | exact resolve b4e469 b4e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e469
          have b4e477 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e474
               have i₂ := b4e193 x
               grind)
            | exact superpose b4e193 b4e474
            | exact resolve b4e474 b4e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193 b4e474
          have b4e478 : False := by grind
          exact b4e478
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X0 X3
               have i₂ := b5e13 X1 X0 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op y X0) := by
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
          have b5e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X1 (M.op (M.op X1 X2) X0)
               have i₂ := b5e13 (M.op X1 X2) X0 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            grind
          have b5e39 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 X1
               have i₂ := b5e32 X0
               grind)
            | exact superpose b5e32 b5e32
            | exact resolve b5e32 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e49 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e51 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e49
          have b5e52 : x = (k x y) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e21
               grind)
            | exact resolve b5e51 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e67 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e84 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 y)) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 y X2
               have i₂ := b5e39 X1 X0
               grind)
            | (have i₁ := b5e13 X1 y X2
               have i₂ := b5e39 X0 X1
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e85 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e39 x X0
               grind)
            | (have i₁ := b5e22
               have i₂ := b5e39 X0 x
               grind)
            | exact superpose b5e39 b5e22
            | exact resolve b5e22 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e86 : ∀ X1 X2 : G, (M.op y X2) = (M.op X1 (M.op X1 y)) := by
            intro X1 X2
            first
            | (have i₁ := b5e84 x X1 X2
               have i₂ := b5e85 x
               grind)
            | exact superpose b5e85 b5e84
            | exact resolve b5e84 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e92 : ∀ X1 : G, y = (M.op X1 (M.op X1 y)) := by
            intro X1
            first
            | (have i₁ := b5e86 X1 x
               have i₂ := b5e85 x
               grind)
            | exact superpose b5e85 b5e86
            | exact resolve b5e86 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85 b5e86
          have b5e118 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e27 X1 X0
               grind)
            | exact superpose b5e27 b5e14
            | exact resolve b5e14 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e184 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e30 X0 X1 (M.op (M.op X0 X1) y) X2
               have i₂ := b5e92 (M.op X0 X1)
               grind)
            | exact superpose b5e92 b5e30
            | exact resolve b5e30 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e185 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (M.op (M.op X1 X0) y)
               have i₂ := b5e92 (M.op X1 X0)
               grind)
            | exact superpose b5e92 b5e13
            | exact resolve b5e13 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92
          have b5e381 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (k (M.op X1 X2) (M.op (M.op X0 (M.op X1 X2)) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36 X2 X1
               have i₂ := b5e35 X0 X1 X2 X3
               grind)
            | exact superpose b5e35 b5e36
            | exact resolve b5e36 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e36
          have b5e405 : ∀ X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) y) := by
            intro X1 X2
            first
            | (have i₁ := b5e381 x X1 X2 x
               have i₂ := b5e184 x (M.op X1 X2) x
               grind)
            | exact superpose b5e184 b5e381
            | exact resolve b5e381 b5e184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e381
          have b5e1804 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e67 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67
          have b5e1805 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1804
               have r₂ := b5e24
               grind)
            | exact resolve b5e1804 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1804
          have b5e1806 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1805
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1805
            | exact resolve b5e1805 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1805
          have b5e1807 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1806
               have i₂ := b5e52
               grind)
            | exact superpose b5e52 b5e1806
            | exact resolve b5e1806 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e1806
          have b5e1825 : ∀ X0 : G, y = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e184 (σ x) (σ y) X0
               have i₂ := b5e1807
               grind)
            | exact superpose b5e1807 b5e184
            | exact resolve b5e184 b5e1807
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e184
          have b5e1827 : (σ x) = (k (σ x) y) := by
            first
            | (have i₁ := b5e405 (σ x) (σ y)
               have i₂ := b5e1807
               grind)
            | exact superpose b5e1807 b5e405
            | exact resolve b5e405 b5e1807
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e405
          have b5e2206 : y = (σ x) := by
            first
            | (have i₁ := b5e1807
               have i₂ := b5e1825 (σ y)
               grind)
            | exact superpose b5e1825 b5e1807
            | exact resolve b5e1807 b5e1825
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1807 b5e1825
          have b5e2879 : x = (τ y) := by
            first
            | (have i₁ := b5e14 x
               have i₂ := b5e2206
               grind)
            | exact superpose b5e2206 b5e14
            | exact resolve b5e14 b5e2206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2206
          have b5e2982 : (τ (σ x)) = (k x (τ y)) := by
            first
            | (have i₁ := b5e118 x y
               have i₂ := b5e1827
               grind)
            | exact superpose b5e1827 b5e118
            | exact resolve b5e118 b5e1827
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118 b5e1827
          have b5e2986 : (k x x) = (τ (σ x)) := by
            first
            | (have i₁ := b5e2982
               have i₂ := b5e2879
               grind)
            | exact superpose b5e2879 b5e2982
            | exact resolve b5e2982 b5e2879
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2879 b5e2982
          have b5e2988 : x = (k x x) := by
            first
            | (have i₁ := b5e2986
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e2986
            | exact resolve b5e2986 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2986
          have b5e3263 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e2988
               grind)
            | exact superpose b5e2988 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e2988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2988
          have b5e3264 : x = (M.op x x) := by grind
          clear b5e3263
          have b5e3458 : y = (M.op x x) := by
            first
            | (have i₁ := b5e185 x x
               have i₂ := b5e3264
               grind)
            | exact superpose b5e3264 b5e185
            | exact resolve b5e185 b5e3264
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e185 b5e3264
          have b5e3460 : False := by grind
          exact b5e3460
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
        have b6e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 X0 X3
             have i₂ := b6e12 X1 X0 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e91 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e101 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e91
             have r₂ := b6e20
             grind)
          | exact resolve b6e91 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e91
        have b6e104 : x = (M.op x y) := by
          first
          | (have r₁ := b6e101
             have r₂ := b6e21
             grind)
          | exact resolve b6e101 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e101
        have b6e122 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e43 x y x x
             have i₂ := b6e104
             grind)
          | exact superpose b6e104 b6e43
          | exact resolve b6e43 b6e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e230 : ∀ X0 : G, x = (k x (M.op x X0)) := by
          intro X0
          grind
        have b6e236 : ∀ X0 : G, y ≠ (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e20
             have i₂ := b6e122 x X0
             grind)
          | (have i₁ := b6e20
             have i₂ := b6e122 X0 x
             grind)
          | exact superpose b6e122 b6e20
          | exact resolve b6e20 b6e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e238 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e104
             have i₂ := b6e122 y X0
             grind)
          | (have i₁ := b6e104
             have i₂ := b6e122 X0 y
             grind)
          | exact superpose b6e122 b6e104
          | exact resolve b6e104 b6e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104 b6e122
        have b6e239 : x ≠ y := by
          first
          | (have i₁ := b6e236 x
             have i₂ := b6e238 x
             grind)
          | exact superpose b6e238 b6e236
          | exact resolve b6e236 b6e238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e236
        have b6e244 : x = (k x x) := by
          first
          | (have i₁ := b6e230 x
             have i₂ := b6e238 x
             grind)
          | exact superpose b6e238 b6e230
          | exact resolve b6e230 b6e238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e230 b6e238
        have b6e2277 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e89 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e89
          | exact resolve b6e89 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e2378 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
        clear b6e2277
        have b6e2431 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2378
             have i₂ := b6e244
             grind)
          | exact superpose b6e244 b6e2378
          | exact resolve b6e2378 b6e244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e244 b6e2378
        have b6e2432 : (σ x) = (σ y) := by grind
        clear b6e2431
        have b6e2514 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e2432
             grind)
          | exact superpose b6e2432 b6e13
          | exact resolve b6e13 b6e2432
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2432
        have b6e2527 : x = y := by
          first
          | (have i₁ := b6e2514
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e2514
          | exact resolve b6e2514 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2514
        have b6e2533 : False := by grind
        exact b6e2533
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e19
            | exact resolve b7e19 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X1) X3) = (M.op X1 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 (M.op X1 X0) X3
               have i₂ := b7e13 X1 X0 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X0 X3
               have i₂ := b7e13 X1 X0 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X1 X0) X1 X3
               have i₂ := b7e13 X1 X0 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 X1 (M.op (M.op X1 X2) X0)
               have i₂ := b7e13 (M.op X1 X2) X0 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            grind
          have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e34 X0 X1 X2 X3
               have i₂ := b7e13 X0 X1 (M.op (M.op X1 X0) X1)
               grind)
            | exact superpose b7e13 b7e34
            | exact resolve b7e34 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e46 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e49 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e46
          have b7e51 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e49
               have r₂ := b7e23
               grind)
            | exact resolve b7e49 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e52 : (σ x) = (σ (k x y)) := by
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
          have b7e55 : (k x y) = (τ (σ x)) := by
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
          have b7e56 : x = (k x y) := by
            first
            | (have i₁ := b7e55
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e55
            | exact resolve b7e55 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e74 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e56
               grind)
            | exact superpose b7e56 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e75 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e21
               grind)
            | exact resolve b7e74 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e77 : x = (M.op x y) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e22
               grind)
            | exact resolve b7e75 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e85 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e27 X1 X0
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e102 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e31 x y x x
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e31
            | exact resolve b7e31 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e164 : ∀ X0 : G, y ≠ (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e21
               have i₂ := b7e102 x X0
               grind)
            | (have i₁ := b7e21
               have i₂ := b7e102 X0 x
               grind)
            | exact superpose b7e102 b7e21
            | exact resolve b7e21 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e166 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e77
               have i₂ := b7e102 y X0
               grind)
            | (have i₁ := b7e77
               have i₂ := b7e102 X0 y
               grind)
            | exact superpose b7e102 b7e77
            | exact resolve b7e77 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e167 : x ≠ y := by
            first
            | (have i₁ := b7e164 x
               have i₂ := b7e166 x
               grind)
            | exact superpose b7e166 b7e164
            | exact resolve b7e164 b7e166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e164
          have b7e225 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op x X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e36 x X1 X2 X3
               have i₂ := b7e102 (M.op X1 X2) X0
               grind)
            | (have i₁ := b7e36 x X1 X2 X3
               have i₂ := b7e102 X0 (M.op X1 X2)
               grind)
            | exact superpose b7e102 b7e36
            | exact resolve b7e36 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e102
          have b7e271 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X2 X1)) = (M.op x X3) := by
            intro X1 X2 X3
            first
            | (have i₁ := b7e225 x X1 X2 X3
               have i₂ := b7e166 x
               grind)
            | exact superpose b7e166 b7e225
            | exact resolve b7e225 b7e166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e225
          have b7e283 : ∀ X1 X2 : G, x = (M.op X2 (M.op X2 X1)) := by
            intro X1 X2
            first
            | (have i₁ := b7e271 X1 X2 x
               have i₂ := b7e166 x
               grind)
            | exact superpose b7e166 b7e271
            | exact resolve b7e271 b7e166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e166 b7e271
          have b7e320 : (σ y) = (k (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
            first
            | (have i₁ := b7e37 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e37
            | exact resolve b7e37 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e374 : (σ y) = (k (σ y) x) := by
            first
            | (have i₁ := b7e320
               have i₂ := b7e283 (σ y) (σ x)
               grind)
            | exact superpose b7e283 b7e320
            | exact resolve b7e320 b7e283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e320
          have b7e586 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X2 (M.op X0 X1)) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e29 (M.op X0 X1) X2 x X3
               have i₂ := b7e38 X0 X1 X2 x
               grind)
            | exact superpose b7e38 b7e29
            | exact resolve b7e29 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e677 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e586 X0 X1 X2 x
               have i₂ := b7e38 X2 (M.op X0 X1) X2 x
               grind)
            | exact superpose b7e38 b7e586
            | exact resolve b7e586 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e586
          have b7e719 : ∀ X0 X1 X2 : G, x = (M.op X2 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e677 X0 X1 X2
               have i₂ := b7e283 (M.op X0 X1) X2
               grind)
            | exact superpose b7e283 b7e677
            | exact resolve b7e677 b7e283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e677
          have b7e746 : ∀ X2 : G, x = (M.op X2 x) := by
            intro X2
            first
            | (have i₁ := b7e719 x x X2
               have i₂ := b7e283 x x
               grind)
            | exact superpose b7e283 b7e719
            | exact resolve b7e719 b7e283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e283 b7e719
          have b7e798 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e31 X0 X1 x X2
               have i₂ := b7e746 (M.op X0 X1)
               grind)
            | exact superpose b7e746 b7e31
            | exact resolve b7e31 b7e746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e746
          have b7e1505 : ∀ X0 : G, x = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e798 (σ y) (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e798
            | exact resolve b7e798 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1617 : x = (σ y) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e1505 (σ x)
               grind)
            | exact superpose b7e1505 b7e24
            | exact resolve b7e24 b7e1505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1505
          have b7e1810 : y = (τ x) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e1617
               grind)
            | exact superpose b7e1617 b7e14
            | exact resolve b7e14 b7e1617
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1617
          have b7e3947 : (τ (σ y)) = (k y (τ x)) := by
            first
            | (have i₁ := b7e85 y x
               have i₂ := b7e374
               grind)
            | exact superpose b7e374 b7e85
            | exact resolve b7e85 b7e374
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85 b7e374
          have b7e3966 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e3947
               have i₂ := b7e1810
               grind)
            | exact superpose b7e1810 b7e3947
            | exact resolve b7e3947 b7e1810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1810 b7e3947
          have b7e3972 : y = (k y y) := by
            first
            | (have i₁ := b7e3966
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e3966
            | exact resolve b7e3966 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3966
          have b7e3981 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e3972
               grind)
            | exact superpose b7e3972 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e3972
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3972
          have b7e3982 : y = (M.op y y) := by grind
          clear b7e3981
          have b7e4177 : ∀ X0 : G, x = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e798 y y X0
               have i₂ := b7e3982
               grind)
            | exact superpose b7e3982 b7e798
            | exact resolve b7e798 b7e3982
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e798
          have b7e4299 : x = y := by
            first
            | (have i₁ := b7e3982
               have i₂ := b7e4177 y
               grind)
            | exact superpose b7e4177 b7e3982
            | exact resolve b7e3982 b7e4177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3982 b7e4177
          have b7e4300 : False := by grind
          exact b7e4300
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1278 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e66 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e1279 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1278
               have r₂ := b8e24
               grind)
            | exact resolve b8e1278 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1278
          have b8e1280 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1279
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1279
            | exact resolve b8e1279 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1279
          have b8e1283 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1280
               grind)
            | exact superpose b8e1280 b8e20
            | exact resolve b8e20 b8e1280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1280
          have b8e1366 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e1283
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1283
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1283 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1283
          have b8e1367 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e1366
          have b8e1370 : y = (M.op y x) := by
            first
            | (have r₁ := b8e1367
               have r₂ := b8e21
               grind)
            | exact resolve b8e1367 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1367
          have b8e1373 : False := by grind
          exact b8e1373
