import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation4478 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4478 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
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
      have b0e65 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e68 : False := by grind
      exact b0e68
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
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
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
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
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
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e34 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b4e13 X0 x X4 X5
               have i₂ := b4e13 X0 x X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 y X0 x X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
            intro X0 X2
            first
            | (have i₁ := b4e39 x X2
               have i₂ := b4e39 x X0
               grind)
            | (have i₁ := b4e39 X0 x
               have i₂ := b4e39 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e39 b4e39
            | exact resolve b4e39 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e50 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op y X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e13 y x X2 X3
               have i₂ := b4e39 x X0
               grind)
            | (have i₁ := b4e13 y x X2 X3
               have i₂ := b4e39 X0 (M.op x x)
               grind)
            | exact superpose b4e39 b4e13
            | exact resolve b4e13 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e88 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e22
               have i₂ := b4e44 x X0
               grind)
            | (have i₁ := b4e22
               have i₂ := b4e44 X0 x
               grind)
            | exact superpose b4e44 b4e22
            | exact resolve b4e22 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e96 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b4e26
          have b4e101 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e96 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e96
            | exact resolve b4e96 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96
          have b4e102 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b4e101
          have b4e171 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X1 X3) X4) = (M.op X1 (M.op y X0)) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b4e13 X1 (M.op y x) X3 X4
               have i₂ := b4e50 X0 x (M.op y x)
               grind)
            | exact superpose b4e50 b4e13
            | exact resolve b4e13 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e177 : ∀ X1 X3 X4 : G, (M.op (M.op X1 X3) X4) = (M.op X1 y) := by
            intro X1 X3 X4
            first
            | (have i₁ := b4e171 x X1 X3 X4
               have i₂ := b4e88 x
               grind)
            | exact superpose b4e88 b4e171
            | exact resolve b4e171 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88 b4e171
          have b4e209 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ y) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e34 (σ y) X0 X1 (σ x) X2
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e248 : ∀ X2 : G, (M.op (σ y) X2) = (M.op (σ y) y) := by
            intro X2
            first
            | (have i₁ := b4e209 x x X2
               have i₂ := b4e177 (σ y) x x
               grind)
            | exact superpose b4e177 b4e209
            | exact resolve b4e209 b4e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e209
          have b4e283 : (σ y) = (M.op (σ y) y) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e248 (σ x)
               grind)
            | exact superpose b4e248 b4e24
            | exact resolve b4e24 b4e248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e333 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e248 X0
               have i₂ := b4e283
               grind)
            | exact superpose b4e283 b4e248
            | exact resolve b4e248 b4e283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e248 b4e283
          have b4e492 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 (σ y) X1 X2
               have i₂ := b4e333 (σ y)
               grind)
            | exact superpose b4e333 b4e13
            | exact resolve b4e13 b4e333
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e333
          have b4e504 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e492 X0 x x
               have i₂ := b4e177 X0 x x
               grind)
            | exact superpose b4e177 b4e492
            | exact resolve b4e492 b4e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e492
          have b4e799 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e504 (σ x)
               grind)
            | exact superpose b4e504 b4e20
            | exact resolve b4e20 b4e504
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e504
          have b4e2831 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b4e30 (M.op (τ X0) (τ X0))
               have i₂ := b4e102 X0
               grind)
            | exact superpose b4e102 b4e30
            | exact resolve b4e30 b4e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e102
          have b4e2841 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e2831 X0
               have i₂ := b4e177 (τ X0) (τ X0) (M.op (τ X0) (τ X0))
               grind)
            | exact superpose b4e177 b4e2831
            | exact resolve b4e2831 b4e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2831
          have b4e2846 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e2841 X0
               have i₂ := b4e177 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e177 b4e2841
            | exact resolve b4e2841 b4e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e177 b4e2841
          have b4e2851 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e2846 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e2846
            | exact resolve b4e2846 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2846
          have b4e2907 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e799
               have i₂ := b4e2851 x
               grind)
            | exact superpose b4e2851 b4e799
            | (have r₁ := b4e799
               have r₂ := b4e2851 x
               grind)
            | exact resolve b4e799 b4e2851
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e799 b4e2851
          have b4e2922 : False := by grind
          exact b4e2922
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e34 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b5e13 X0 x X4 X5
               have i₂ := b5e13 X0 x X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 y X0 x X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
            intro X0 X2
            first
            | (have i₁ := b5e36 x X2
               have i₂ := b5e36 x X0
               grind)
            | (have i₁ := b5e36 X0 x
               have i₂ := b5e36 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e36 b5e36
            | exact resolve b5e36 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op y X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e13 y x X2 X3
               have i₂ := b5e36 x X0
               grind)
            | (have i₁ := b5e13 y x X2 X3
               have i₂ := b5e36 X0 (M.op x x)
               grind)
            | exact superpose b5e36 b5e13
            | exact resolve b5e13 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e83 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e43 x X0
               grind)
            | (have i₁ := b5e22
               have i₂ := b5e43 X0 x
               grind)
            | exact superpose b5e43 b5e22
            | exact resolve b5e22 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e91 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e26
          have b5e96 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e91 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e91
            | exact resolve b5e91 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91
          have b5e97 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e96
          have b5e166 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X1 X3) X4) = (M.op X1 (M.op y X0)) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b5e13 X1 (M.op y x) X3 X4
               have i₂ := b5e49 X0 x (M.op y x)
               grind)
            | exact superpose b5e49 b5e13
            | exact resolve b5e13 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e172 : ∀ X1 X3 X4 : G, (M.op (M.op X1 X3) X4) = (M.op X1 y) := by
            intro X1 X3 X4
            first
            | (have i₁ := b5e166 x X1 X3 X4
               have i₂ := b5e83 x
               grind)
            | exact superpose b5e83 b5e166
            | exact resolve b5e166 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e166
          have b5e203 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (M.op X0 X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e34 (σ X0) X1 X2 (σ X0) X3
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e34
            | exact resolve b5e34 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e240 : ∀ X0 X3 : G, (M.op (σ (M.op X0 X0)) X3) = (M.op (σ X0) y) := by
            intro X0 X3
            first
            | (have i₁ := b5e203 X0 x x X3
               have i₂ := b5e172 (σ X0) x x
               grind)
            | exact superpose b5e172 b5e203
            | exact resolve b5e203 b5e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e203
          have b5e1465 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e30 (M.op (τ X0) (τ X0))
               have i₂ := b5e97 X0
               grind)
            | exact superpose b5e97 b5e30
            | exact resolve b5e30 b5e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e97
          have b5e1471 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b5e1465 X0
               have i₂ := b5e172 (τ X0) (τ X0) (M.op (τ X0) (τ X0))
               grind)
            | exact superpose b5e172 b5e1465
            | exact resolve b5e1465 b5e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1465
          have b5e1473 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b5e1471 X0
               have i₂ := b5e172 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e172 b5e1471
            | exact resolve b5e1471 b5e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e172 b5e1471
          have b5e1822 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e1473 (σ X0)
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1473
            | exact resolve b5e1473 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1473
          have b5e2609 : ∀ X0 : G, (M.op (σ y) y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e240 y X0
               have i₂ := b5e83 y
               grind)
            | exact superpose b5e83 b5e240
            | exact resolve b5e240 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e240
          have b5e2707 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e2609 X0
               have i₂ := b5e1822 y
               grind)
            | exact superpose b5e1822 b5e2609
            | exact resolve b5e2609 b5e1822
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1822 b5e2609
          have b5e2750 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e2707 X0
               have i₂ := b5e83 y
               grind)
            | exact superpose b5e83 b5e2707
            | exact resolve b5e2707 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83 b5e2707
          have b5e2808 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e2750 (σ x)
               grind)
            | exact superpose b5e2750 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e2750 (σ x)
               grind)
            | exact resolve b5e24 b5e2750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2750
          have b5e2850 : False := by grind
          exact b5e2850
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
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b7e33 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b7e13 X2 (M.op X0 x) X4 X5
               have i₂ := b7e13 X0 X1 x (M.op X0 x)
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ y) X0 (σ x) X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 X1 x x
               have i₂ := b7e13 X0 X2 x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e51 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e48
          have b7e52 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e51
               have r₂ := b7e23
               grind)
            | exact resolve b7e51 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e53 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e52
            | exact resolve b7e52 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e56 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e14
            | exact resolve b7e14 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e57 : x = (k x y) := by
            first
            | (have i₁ := b7e56
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e56
            | exact resolve b7e56 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e67 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e57
               grind)
            | exact superpose b7e57 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e68 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e22
               grind)
            | exact resolve b7e67 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e70 : x = (M.op x y) := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e21
               grind)
            | exact resolve b7e68 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e142 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) := by
            intro X0 X2
            first
            | (have i₁ := b7e36 x X2
               have i₂ := b7e36 x X0
               grind)
            | (have i₁ := b7e36 X0 x
               have i₂ := b7e36 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e36 b7e36
            | exact resolve b7e36 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e183 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e24
               have i₂ := b7e142 (σ x) X0
               grind)
            | (have i₁ := b7e24
               have i₂ := b7e142 X0 (σ x)
               grind)
            | exact superpose b7e142 b7e24
            | exact resolve b7e24 b7e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e142
          have b7e272 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e30 y
               have i₂ := b7e183 (σ y)
               grind)
            | exact superpose b7e183 b7e30
            | exact resolve b7e30 b7e183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e278 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e39 X0 (σ y) X1
               have i₂ := b7e183 (σ y)
               grind)
            | exact superpose b7e183 b7e39
            | exact resolve b7e39 b7e183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e280 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 (σ y) X1 X2
               have i₂ := b7e183 (σ y)
               grind)
            | exact superpose b7e183 b7e13
            | exact resolve b7e13 b7e183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e307 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op x (M.op X1 (M.op X2 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e33 X1 X2 x y X0
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e33
            | exact resolve b7e33 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e325 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X3 (σ y))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e33 X3 (σ y) X0 X1 X2
               have i₂ := b7e183 (σ y)
               grind)
            | exact superpose b7e183 b7e33
            | exact resolve b7e33 b7e183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e183
          have b7e399 : ∀ X0 X3 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X3 (σ y))) := by
            intro X0 X3
            first
            | (have i₁ := b7e325 X0 x x X3
               have i₂ := b7e280 X0 x x
               grind)
            | exact superpose b7e280 b7e325
            | exact resolve b7e325 b7e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e280 b7e325
          have b7e412 : ∀ X0 X1 : G, (M.op x X0) = (M.op x (M.op X1 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e307 X0 X1 x
               have i₂ := b7e278 X1 x
               grind)
            | exact superpose b7e278 b7e307
            | exact resolve b7e307 b7e278
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e278 b7e307
          have b7e436 : ∀ X0 : G, (M.op x X0) = (M.op x (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e412 X0 x
               have i₂ := b7e399 x x
               grind)
            | exact superpose b7e399 b7e412
            | exact resolve b7e412 b7e399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e399 b7e412
          have b7e466 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e272
               grind)
            | exact superpose b7e272 b7e14
            | exact resolve b7e14 b7e272
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e272
          have b7e467 : y = (M.op y y) := by
            first
            | (have i₁ := b7e466
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e466
            | exact resolve b7e466 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e466
          have b7e656 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b7e39 X0 y X1
               have i₂ := b7e467
               grind)
            | exact superpose b7e467 b7e39
            | exact resolve b7e39 b7e467
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e912 : ∀ X0 X1 : G, (M.op x X1) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e436 X1
               have i₂ := b7e436 X0
               grind)
            | (have i₁ := b7e436 X0
               have i₂ := b7e436 (σ y)
               grind)
            | exact superpose b7e436 b7e436
            | exact resolve b7e436 b7e436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e436
          have b7e1168 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op x X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e39 X1 X2 x
               have i₂ := b7e912 X0 x
               grind)
            | (have i₁ := b7e39 X1 X2 x
               have i₂ := b7e912 x X0
               grind)
            | exact superpose b7e912 b7e39
            | exact resolve b7e39 b7e912
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e1186 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e70
               have i₂ := b7e912 X0 y
               grind)
            | (have i₁ := b7e70
               have i₂ := b7e912 y X0
               grind)
            | exact superpose b7e912 b7e70
            | exact resolve b7e70 b7e912
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e912
          have b7e1219 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 x) := by
            intro X1 X2
            first
            | (have i₁ := b7e1168 x X1 X2
               have i₂ := b7e1186 x
               grind)
            | exact superpose b7e1186 b7e1168
            | exact resolve b7e1168 b7e1186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1168 b7e1186
          have b7e1228 : ∀ X1 : G, (M.op X1 y) = (M.op X1 x) := by
            intro X1
            first
            | (have i₁ := b7e1219 X1 x
               have i₂ := b7e656 X1 x
               grind)
            | exact superpose b7e656 b7e1219
            | exact resolve b7e1219 b7e656
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e656 b7e1219
          have b7e1678 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e1228 y
               grind)
            | exact superpose b7e1228 b7e22
            | exact resolve b7e22 b7e1228
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1228
          have b7e1679 : False := by grind
          exact b7e1679
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e1180 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e62 x y
               grind)
            | exact superpose b8e62 b8e20
            | (have j1 := b8e62 x y
               grind)
            | exact resolve b8e20 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e1217 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e1180
               have r₂ := b8e24
               grind)
            | exact resolve b8e1180 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1180
          have b8e1226 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1217
               have r₂ := b8e23
               grind)
            | exact resolve b8e1217 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1217
          have b8e1231 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e1226
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1226
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e1226
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1226
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1226 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1226
          have b8e1232 : y = (M.op y x) ∨ x = y := by grind
          clear b8e1231
          have b8e1233 : x = y := by
            first
            | (have r₁ := b8e1232
               have r₂ := b8e22
               grind)
            | exact resolve b8e1232 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1232
          have b8e1234 : False := by grind
          exact b8e1234

/-- `Equation4490`: `x ◇ (y ◇ y) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pyx_x_pxy_Equation4490 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4490 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4490.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 (M.op X1 X1) X3
           have i₂ := b0e11 (M.op X1 X1) X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X2 X3
           have i₂ := b0e11 X1 X2 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X2 X2) X3 X1
           have i₂ := b0e11 X1 X2 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 (M.op x X0)
           have i₂ := b0e11 X0 X1 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e11 x X0 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 (M.op X3 X3) X1
           have i₂ := b0e11 (M.op X1 X2) X3 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e27 x X1 X2 X3
           have i₂ := b0e32 x X1 X1
           grind)
        | exact superpose b0e32 b0e27
        | exact resolve b0e27 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e40 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X0 X1
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e11
        | exact resolve b0e11 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op X0 X0) X1 x
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e11
        | exact resolve b0e11 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
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
      have b0e46 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k x X0) := by
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
      have b0e47 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e46 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e48 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e45 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e16 (σ X0) (σ X1)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X0) (σ X0)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X2
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X1
           have j1 := b0e16 X0 X2
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X1 X1
           have r₂ := b0e16 X1 X1
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = X2 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e65 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65
      have b0e98 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k X0 (τ X1))
           have i₂ := b0e22 X1 X0
           grind)
        | exact superpose b0e22 b0e12
        | exact resolve b0e12 b0e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e171 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e29 X0 (σ x) X1 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e29
        | exact resolve b0e29 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e174 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X2) = (M.op (M.op X1 (M.op X0 X0)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e29 X1 (M.op X0 X0) X2 x
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e29
        | exact resolve b0e29 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e204 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X4 (M.op X3 X1)) X2) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 (M.op X3 X1) X2 X4
           have i₂ := b0e29 X3 X1 (M.op X2 X2) X0
           grind)
        | (have i₁ := b0e11 (M.op X3 X1) X2 X4
           have i₂ := b0e29 X0 X1 (M.op X2 X2) X3
           grind)
        | exact superpose b0e29 b0e11
        | exact resolve b0e11 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e212 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 (σ x))) := by
        intro X0
        first
        | (have i₁ := b0e98 x X0
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e98
        | exact resolve b0e98 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e98
      have b0e221 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 (σ x))) := by
        intro X0
        first
        | (have i₁ := b0e212 X0
           have i₂ := b0e47 (τ X0)
           grind)
        | exact superpose b0e47 b0e212
        | exact resolve b0e212 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e212
      have b0e548 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X1 X1)) = (M.op X3 (M.op (M.op X0 X1) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e36 X1 X3 X2
           have i₂ := b0e11 X1 X1 X0
           grind)
        | exact superpose b0e11 b0e36
        | exact resolve b0e36 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e567 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (M.op X1 X1) x
           have i₂ := b0e36 X1 X0 x
           grind)
        | exact superpose b0e36 b0e11
        | exact resolve b0e11 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e576 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e31 X2 X3 (M.op X0 X0) X1
           have i₂ := b0e36 X0 X0 X0
           grind)
        | exact superpose b0e36 b0e31
        | exact resolve b0e31 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e601 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 (M.op X2 X2))) X4) = (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e29 X3 (M.op X2 (M.op X2 X2)) X4 X1
           have i₂ := b0e36 X2 X1 X0
           grind)
        | exact superpose b0e36 b0e29
        | exact resolve b0e29 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e615 : ∀ X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 (M.op X2 X2))) X4) = (M.op (M.op x X2) X4) := by
        intro X2 X3 X4
        first
        | (have i₁ := b0e601 x x X2 X3 X4
           have i₂ := b0e174 X2 (M.op x x) X4
           grind)
        | exact superpose b0e174 b0e601
        | exact resolve b0e601 b0e174
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e601
      have b0e629 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e576 X0 X1 x x
           have i₂ := b0e174 X0 (M.op x x) X1
           grind)
        | exact superpose b0e174 b0e576
        | exact resolve b0e576 b0e174
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e174 b0e576
      have b0e633 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e567 X0 X1
           have i₂ := b0e36 X1 X1 X1
           grind)
        | exact superpose b0e36 b0e567
        | exact resolve b0e567 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e567
      have b0e664 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x X0) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e629 X0 X1
           have i₂ := b0e615 X0 X0 (M.op X1 X1)
           grind)
        | (have i₁ := b0e629 x X1
           have i₂ := b0e615 (M.op x (M.op x x)) x (M.op X1 X1)
           grind)
        | exact superpose b0e615 b0e629
        | exact resolve b0e629 b0e615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e615 b0e629
      have b0e727 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X4 X4) (M.op X4 X4))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b0e35 X2 (M.op x X0) (M.op X1 X1) X4
           have i₂ := b0e36 X1 X0 x
           grind)
        | exact superpose b0e36 b0e35
        | exact resolve b0e35 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e758 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X2 X2)) = (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e35 (M.op x x) X0 X1 X2
           have i₂ := b0e31 x x (M.op X0 X1) X2
           grind)
        | exact superpose b0e31 b0e35
        | exact resolve b0e35 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e780 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) X1) = (M.op X4 (M.op (M.op X0 X1) (M.op X1 X1))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e35 X2 X3 X4 X1
           have i₂ := b0e29 X1 X1 (M.op X1 X1) X0
           grind)
        | (have i₁ := b0e35 X2 X3 X4 X1
           have i₂ := b0e29 X0 X1 (M.op X1 X1) X1
           grind)
        | exact superpose b0e29 b0e35
        | exact resolve b0e35 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e799 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 x X0 X1
           have i₂ := b0e35 x X0 X0 X1
           grind)
        | exact superpose b0e35 b0e32
        | exact resolve b0e32 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e825 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X3 (M.op (M.op X2 X2) (M.op X2 X2)) X4
           have i₂ := b0e35 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e876 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e825 X0 X1 X1 X3 X4
           have i₂ := b0e36 X1 X1 X1
           grind)
        | exact superpose b0e36 b0e825
        | exact resolve b0e825 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e825
      have b0e895 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e799 X0 X1
           have i₂ := b0e36 X1 X1 X1
           grind)
        | exact superpose b0e36 b0e799
        | exact resolve b0e799 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e799
      have b0e922 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X2 X2)) = (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e758 X0 X1 X2
           have i₂ := b0e36 X2 X2 X2
           grind)
        | exact superpose b0e36 b0e758
        | exact resolve b0e758 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e758
      have b0e946 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X1) (M.op X4 X4)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b0e727 X0 X1 X2 X4
           have i₂ := b0e41 X1 (M.op X4 X4)
           grind)
        | exact superpose b0e41 b0e727
        | exact resolve b0e727 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e727
      have b0e973 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e876 X0 X1 X2 X3 X4
           have i₂ := b0e633 X1 X2
           grind)
        | exact superpose b0e633 b0e876
        | exact resolve b0e876 b0e633
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e876
      have b0e1008 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X2 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e922 X0 X1 X2
           have i₂ := b0e895 X1 X2
           grind)
        | exact superpose b0e895 b0e922
        | exact resolve b0e922 b0e895
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e895 b0e922
      have b0e1018 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) = (M.op (M.op x X1) X4) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b0e946 X0 X1 X2 X4
           have i₂ := b0e664 X1 X4
           grind)
        | exact superpose b0e664 b0e946
        | exact resolve b0e946 b0e664
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e946
      have b0e1034 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) = (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e973 X0 X1 X2 X3 X4
           have i₂ := b0e633 (M.op X4 X3) X2
           grind)
        | exact superpose b0e633 b0e973
        | exact resolve b0e973 b0e633
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e973
      have b0e1057 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op x (M.op X0 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1008 X0 X1 X2
           have i₂ := b0e41 (M.op X0 X1) X2
           grind)
        | exact superpose b0e41 b0e1008
        | exact resolve b0e1008 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1008
      have b0e1072 : ∀ X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) = (M.op X3 (M.op (M.op x X2) X2)) := by
        intro X2 X3 X4
        first
        | (have i₁ := b0e1034 x x X2 X3 X4
           have i₂ := b0e1018 x X2 x X2
           grind)
        | exact superpose b0e1018 b0e1034
        | exact resolve b0e1034 b0e1018
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1018 b0e1034
      have b0e1202 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e70 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e2158 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X0) X1
           have i₂ := b0e61 X0 X0
           grind)
        | exact superpose b0e61 b0e14
        | (have j0 := b0e14 (σ X0) X1
           have j1 := b0e61 X0 X0
           grind)
        | (have r₁ := b0e14 (σ X0) X1
           have r₂ := b0e61 X0 X1
           grind)
        | (have r₁ := b0e14 (σ X1) X1
           have r₂ := b0e61 X1 X1
           grind)
        | exact resolve b0e14 b0e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e2222 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e2158 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2158
      have b0e2233 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e2222 X0 X1
           have j1 := b0e14 (σ X0) X1
           grind)
        | (have r₁ := b0e2222 X0 X1
           have r₂ := b0e14 (σ X0) X1
           grind)
        | exact resolve b0e2222 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2222
      have b0e2733 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op x X1) (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X1 (M.op X0 X0)
           have i₂ := b0e36 X0 X0 X0
           grind)
        | exact superpose b0e36 b0e41
        | exact resolve b0e41 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2764 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op X3 (M.op (M.op x X0) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e35 X1 X2 X3 X0
           have i₂ := b0e41 X0 X0
           grind)
        | exact superpose b0e41 b0e35
        | exact resolve b0e35 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e2765 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 X1 X0 X0
           have i₂ := b0e41 X0 X1
           grind)
        | exact superpose b0e41 b0e36
        | exact resolve b0e36 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2773 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 X1)) = (M.op (M.op x X0) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e29 X0 X0 (M.op X1 X1) X2
           have i₂ := b0e41 X0 X1
           grind)
        | exact superpose b0e41 b0e29
        | exact resolve b0e29 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29 b0e41
      have b0e2851 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e2733 X0 X1
           have i₂ := b0e2773 X1 X0 x
           grind)
        | exact superpose b0e2773 b0e2733
        | exact resolve b0e2733 b0e2773
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2733
      have b0e2869 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e2851 X0 X1
           have i₂ := b0e633 (M.op X1 X1) X0
           grind)
        | exact superpose b0e633 b0e2851
        | exact resolve b0e2851 b0e633
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e633 b0e2851
      have b0e2878 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X1 (M.op (M.op x X0) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e2869 X0 X1
           have i₂ := b0e1072 X0 X1 X1
           grind)
        | exact superpose b0e1072 b0e2869
        | exact resolve b0e2869 b0e1072
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1072 b0e2869
      have b0e5366 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op x (M.op X0 X1)) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X2 X3
           have i₂ := b0e1057 X0 X1 X2
           grind)
        | exact superpose b0e1057 b0e11
        | exact resolve b0e11 b0e1057
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1057
      have b0e7736 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op (M.op x X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e664 X2 X3
           have i₂ := b0e204 x X2 X3 X1 X0
           grind)
        | exact superpose b0e204 b0e664
        | exact resolve b0e664 b0e204
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e204 b0e664
      have b0e8309 : ∀ X0 X1 X2 : G, (M.op (M.op x X2) X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e2765 X2 X1
           have i₂ := b0e11 X1 X1 X0
           grind)
        | exact superpose b0e11 b0e2765
        | exact resolve b0e2765 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e10169 : ∀ X0 X1 : G, (M.op (M.op x X0) X0) ≠ (M.op (M.op x (M.op (M.op x X0) X0)) X0) ∨ (M.op X1 (M.op (M.op x X0) X0)) = (k (M.op (M.op x X0) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (M.op (M.op x X0) X0) X1
           have i₂ := b0e2878 X0 (M.op (M.op x X0) X0)
           grind)
        | exact superpose b0e2878 b0e14
        | (have j0 := b0e14 (M.op (M.op x X0) X0) X1
           grind)
        | exact resolve b0e14 b0e2878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e10329 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) X0)) = (k (M.op (M.op x X0) X0) X1) := by
        intro X0 X1
        first
        | (have j0 := b0e10169 X0 X1
           grind)
        | (have r₁ := b0e10169 x X1
           have r₂ := b0e5366 (M.op x x) x x x
           grind)
        | exact resolve b0e10169 b0e5366
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10169
      have b0e10397 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (k (M.op (M.op x X0) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10329 X0 X1
           have i₂ := b0e2878 X0 X1
           grind)
        | exact superpose b0e2878 b0e10329
        | exact resolve b0e10329 b0e2878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10329
      have b0e10852 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X2) ≠ (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X2 X2)) ∨ (k (M.op (M.op X1 X2) X2) X3) = (M.op X3 (M.op (M.op X1 X2) X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e14 (M.op (M.op X1 X2) X2) X3
           have i₂ := b0e548 X1 X2 X0 (M.op (M.op X1 X2) X2)
           grind)
        | exact superpose b0e548 b0e14
        | (have j0 := b0e14 (M.op (M.op X1 X2) X2) X3
           grind)
        | exact resolve b0e14 b0e548
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e548
      have b0e11035 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X2) ≠ (M.op (M.op x (M.op (M.op X1 X2) X2)) X2) ∨ (k (M.op (M.op X1 X2) X2) X3) = (M.op X3 (M.op (M.op X1 X2) X2)) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e10852 x X1 X2 X3
           have i₂ := b0e2773 (M.op (M.op X1 X2) X2) X2 x
           grind)
        | exact superpose b0e2773 b0e10852
        | (have j0 := b0e10852 x X1 X2 X3
           grind)
        | exact resolve b0e10852 b0e2773
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2773 b0e10852
      have b0e11361 : ∀ X1 X2 X3 : G, (k (M.op (M.op X1 X2) X2) X3) = (M.op X3 (M.op (M.op X1 X2) X2)) := by
        intro X1 X2 X3
        first
        | (have j0 := b0e11035 X1 X2 X3
           grind)
        | (have r₁ := b0e11035 X3 X2 X3
           have r₂ := b0e5366 (M.op X3 X2) X2 X2 X3
           grind)
        | exact resolve b0e11035 b0e5366
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5366 b0e11035
      have b0e11547 : ∀ X1 X2 X3 : G, (M.op (M.op x X3) X2) = (k (M.op (M.op X1 X2) X2) X3) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e11361 X1 X2 X3
           have i₂ := b0e8309 X1 X2 X3
           grind)
        | exact superpose b0e8309 b0e11361
        | exact resolve b0e11361 b0e8309
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8309 b0e11361
      have b0e66205 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X2 X1) X1)) X0) = (σ (M.op (M.op x (τ X0)) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e22 X0 (M.op (M.op X2 X1) X1)
           have i₂ := b0e11547 X2 X1 (τ X0)
           grind)
        | exact superpose b0e11547 b0e22
        | exact resolve b0e22 b0e11547
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e11547
      have b0e75517 : ∀ X0 X1 : G, (σ (M.op (M.op x X0) X0)) ≠ (σ (M.op (M.op x (M.op (M.op x X0) X0)) X0)) ∨ (k (σ (M.op (M.op x X0) X0)) X1) = (M.op X1 (σ (M.op (M.op x X0) X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e2233 (M.op (M.op x X0) X0) X1
           have i₂ := b0e10397 X0 (M.op (M.op x X0) X0)
           grind)
        | exact superpose b0e10397 b0e2233
        | (have j0 := b0e2233 (M.op (M.op x X0) X0) X1
           grind)
        | exact resolve b0e2233 b0e10397
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2233 b0e10397
      have b0e75535 : ∀ X0 X1 : G, (σ (M.op (M.op x X0) X0)) ≠ (σ (M.op X0 (M.op (M.op x X0) X0))) ∨ (k (σ (M.op (M.op x X0) X0)) X1) = (M.op X1 (σ (M.op (M.op x X0) X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e75517 X0 X1
           have i₂ := b0e2764 X0 x (M.op x X0) X0
           grind)
        | exact superpose b0e2764 b0e75517
        | (have j0 := b0e75517 X0 X1
           grind)
        | exact resolve b0e75517 b0e2764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2764 b0e75517
      have b0e75615 : ∀ X0 X1 : G, (σ (M.op (M.op x X0) X0)) ≠ (σ (M.op (M.op x X0) X0)) ∨ (k (σ (M.op (M.op x X0) X0)) X1) = (M.op X1 (σ (M.op (M.op x X0) X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e75535 X0 X1
           have i₂ := b0e2878 X0 X0
           grind)
        | exact superpose b0e2878 b0e75535
        | (have j0 := b0e75535 X0 X1
           grind)
        | exact resolve b0e75535 b0e2878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2878 b0e75535
      have b0e75616 : ∀ X0 X1 : G, (k (σ (M.op (M.op x X0) X0)) X1) = (M.op X1 (σ (M.op (M.op x X0) X0))) := by
        intro X0 X1
        first
        | (have j0 := b0e75615 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75615
      have b0e75671 : ∀ X0 X1 : G, (σ (M.op (M.op x (τ X1)) X0)) = (M.op X1 (σ (M.op (M.op x X0) X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e75616 X0 X1
           have i₂ := b0e66205 X1 X0 x
           grind)
        | exact superpose b0e66205 b0e75616
        | exact resolve b0e75616 b0e66205
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66205 b0e75616
      have b0e118556 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e1202 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1202
      have b0e118557 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e118556 X0
           have j1 := b0e14 X0 X0
           grind)
        | (have r₁ := b0e118556 X0
           have r₂ := b0e14 X0 x
           grind)
        | exact resolve b0e118556 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118556
      have b0e119091 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e118557 (σ X0)
           grind)
        | exact superpose b0e118557 b0e17
        | exact resolve b0e17 b0e118557
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e119106 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e119091 X0
           have i₂ := b0e118557 X0
           grind)
        | exact superpose b0e118557 b0e119091
        | exact resolve b0e119091 b0e118557
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118557 b0e119091
      have b0e120853 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (σ X0)) = (M.op X3 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e780 (σ X0) (σ X0) X2 X3 x
           have i₂ := b0e119106 X0
           grind)
        | exact superpose b0e119106 b0e780
        | exact resolve b0e780 b0e119106
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e780
      have b0e120933 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (σ X0)) = (M.op X3 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e120853 X0 X1 X2 X3
           have i₂ := b0e119106 (M.op X0 X0)
           grind)
        | exact superpose b0e119106 b0e120853
        | exact resolve b0e120853 b0e119106
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e119106 b0e120853
      have b0e121028 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (σ X0)) = (M.op X3 (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e120933 X0 X1 X2 X3
           have i₂ := b0e36 X0 X0 X0
           grind)
        | exact superpose b0e36 b0e120933
        | exact resolve b0e120933 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e120933
      have b0e121076 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (σ X0)) = (M.op X3 (σ (M.op (M.op x X0) X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e121028 X0 X1 X2 X3
           have i₂ := b0e2765 X0 X0
           grind)
        | exact superpose b0e2765 b0e121028
        | exact resolve b0e121028 b0e2765
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2765 b0e121028
      have b0e121099 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (σ X0)) = (σ (M.op (M.op x (τ X3)) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e121076 X0 X1 X2 X3
           have i₂ := b0e75671 X0 X3
           grind)
        | exact superpose b0e75671 b0e121076
        | exact resolve b0e121076 b0e75671
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75671 b0e121076
      have b0e121106 : ∀ X0 X3 : G, (M.op (M.op x X3) (σ X0)) = (σ (M.op (M.op x (τ X3)) X0)) := by
        intro X0 X3
        first
        | (have i₁ := b0e121099 X0 x x X3
           have i₂ := b0e7736 x x X3 (σ X0)
           grind)
        | exact superpose b0e7736 b0e121099
        | exact resolve b0e121099 b0e7736
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e121099
      have b0e381474 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 (σ x))) (σ X1)) = (σ (M.op (M.op x (M.op (τ X0) x)) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e121106 X1 (M.op X0 (σ x))
           have i₂ := b0e221 X0
           grind)
        | exact superpose b0e221 b0e121106
        | exact resolve b0e121106 b0e221
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e221 b0e121106
      have b0e381695 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 (σ x))) (σ X1)) = (σ (M.op (M.op x x) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e381474 X0 X1
           have i₂ := b0e7736 x (τ X0) x X1
           grind)
        | exact superpose b0e7736 b0e381474
        | exact resolve b0e381474 b0e7736
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e381474
      have b0e381765 : ∀ X0 X1 : G, (σ (M.op x X1)) = (M.op (M.op x (M.op X0 (σ x))) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e381695 X0 X1
           have i₂ := b0e40 X1 x
           grind)
        | exact superpose b0e40 b0e381695
        | exact resolve b0e381695 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e381695
      have b0e381816 : ∀ X1 : G, (σ (M.op x X1)) = (M.op (M.op x (σ x)) (σ X1)) := by
        intro X1
        first
        | (have i₁ := b0e381765 x X1
           have i₂ := b0e7736 x x (σ x) (σ X1)
           grind)
        | exact superpose b0e7736 b0e381765
        | exact resolve b0e381765 b0e7736
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7736 b0e381765
      have b0e381851 : ∀ X1 : G, (M.op (σ x) (σ X1)) = (σ (M.op x X1)) := by
        intro X1
        first
        | (have i₁ := b0e381816 X1
           have i₂ := b0e171 x (σ X1)
           grind)
        | exact superpose b0e171 b0e381816
        | exact resolve b0e381816 b0e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e171 b0e381816
      have b0e382342 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e381851 y
           grind)
        | exact superpose b0e381851 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e381851 y
           grind)
        | exact resolve b0e18 b0e381851
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e381851
      have b0e382578 : False := by grind
      exact b0e382578
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e43 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k x X0) := by
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
        have b1e44 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X0 X1
             have i₂ := b1e17 (σ X0) (σ X1)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X0)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2556 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e65 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e2558 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e2556 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2556
        have b1e32381 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e2558 x
             have i₂ := b1e44 x
             grind)
          | exact superpose b1e44 b1e2558
          | (have j0 := b1e2558 x
             grind)
          | exact resolve b1e2558 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e2558
        have b1e32387 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have r₁ := b1e32381
             have r₂ := b1e21
             grind)
          | exact resolve b1e32381 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32381
        have b1e32394 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e32387
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e32387
          | exact resolve b1e32387 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32387
        have b1e32395 : False := by grind
        exact b1e32395
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e40 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k x X0) := by
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
        have b2e42 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2537 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e66 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e2539 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e2537 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2537
        have b2e23337 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e2539 x
             have i₂ := b2e42 x
             grind)
          | exact superpose b2e42 b2e2539
          | (have j0 := b2e2539 x
             grind)
          | exact resolve b2e2539 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e2539
        have b2e23343 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have r₁ := b2e23337
             have r₂ := b2e21
             grind)
          | exact resolve b2e23337 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23337
        have b2e23348 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e23343
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e23343
          | exact resolve b2e23343 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23343
        have b2e23349 : False := by grind
        exact b2e23349
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e43 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
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
        have b3e44 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e47 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e44 (σ X0)
             grind)
          | exact superpose b3e44 b3e18
          | exact resolve b3e18 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e116 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e47 x
             grind)
          | exact superpose b3e47 b3e22
          | exact resolve b3e22 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e197 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e116
             grind)
          | exact superpose b3e116 b3e13
          | exact resolve b3e13 b3e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e116
        have b3e199 : x = (k x x) := by
          first
          | (have i₁ := b3e197
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e197
          | exact resolve b3e197 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e197
        have b3e222 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e199
             grind)
          | exact superpose b3e199 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e199
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e199
        have b3e223 : x = (M.op x x) := by grind
        clear b3e222
        have b3e225 : False := by grind
        exact b3e225
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b5e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X1 X1) X3
               have i₂ := b5e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X3
               have i₂ := b5e13 X1 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X2 X2) X3 X1
               have i₂ := b5e13 X1 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op x X0)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X3 X3) X1
               have i₂ := b5e13 (M.op X1 X2) X3 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b5e28 x X1 X2 X3
               have i₂ := b5e33 x X1 X1
               grind)
            | exact superpose b5e33 b5e28
            | exact resolve b5e28 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e36 : ∀ X0 X1 : G, (M.op y (M.op X1 X1)) = (M.op y (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e31 (M.op X1 X1)
               have i₂ := b5e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b5e13 b5e31
            | exact resolve b5e31 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X1 : G, (M.op y (M.op X1 X1)) = (M.op y (M.op X1 (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b5e36 x X1
               have i₂ := b5e33 x X1 X1
               grind)
            | exact superpose b5e33 b5e36
            | exact resolve b5e36 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e41 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op X1 (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b5e40 X1
               have i₂ := b5e31 X1
               grind)
            | exact superpose b5e31 b5e40
            | exact resolve b5e40 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e42 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op (M.op X0 (M.op X1 X1)) X1) ∨ (k (M.op X1 X1) X2) = (M.op X2 (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 (M.op X1 X1) X2
               have i₂ := b5e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b5e13 b5e16
            | (have j0 := b5e16 (M.op X1 X1) X2
               grind)
            | exact resolve b5e16 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X1 X2 : G, (M.op X1 X1) ≠ (M.op X1 (M.op X1 X1)) ∨ (k (M.op X1 X1) X2) = (M.op X2 (M.op X1 X1)) := by
            intro X1 X2
            first
            | (have i₁ := b5e42 x X1 X2
               have i₂ := b5e33 x X1 X1
               grind)
            | exact superpose b5e33 b5e42
            | (have j0 := b5e42 x X1 X2
               grind)
            | exact resolve b5e42 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e56 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X1 X1) = X1 ∨ (k X1 (M.op X2 X2)) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X1 (M.op X2 X2)
               have i₂ := b5e13 X1 X2 X0
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 X1 (M.op X2 X2)
               grind)
            | (have r₁ := b5e17 X0 (M.op (M.op X2 X0) (M.op X2 X0))
               have r₂ := b5e13 X0 (M.op X2 X0) X2
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e59 : y ≠ y ∨ x = (M.op x x) ∨ x = (k x y) := by
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
          have b5e61 : x = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e59
          have b5e62 : x = (k x y) := by
            first
            | (have r₁ := b5e61
               have r₂ := b5e21
               grind)
            | exact resolve b5e61 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X0)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e71 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = X2 := by
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
          have b5e77 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) X0
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) x
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ x)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e77 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77
          have b5e79 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e71 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e95 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e128 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X2) = (M.op (M.op X1 (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e29 X1 (M.op X0 X0) X2 y
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e29
            | exact resolve b5e29 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e336 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 (M.op x x) X0 X1
               have i₂ := b5e32 x x (M.op X0 X0) X1
               grind)
            | exact superpose b5e32 b5e33
            | exact resolve b5e33 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e351 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op y X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e336 X0 X1
               have i₂ := b5e128 X0 (M.op X0 X0) (M.op X1 X1)
               grind)
            | exact superpose b5e128 b5e336
            | exact resolve b5e336 b5e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e336
          have b5e385 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op (M.op X2 (M.op X0 (M.op X0 X0))) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e29 y (M.op X0 (M.op X0 X0)) X1 X2
               have i₂ := b5e41 X0
               grind)
            | exact superpose b5e41 b5e29
            | exact resolve b5e29 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e411 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 X1 (M.op X0 (M.op X0 X0)) y
               have i₂ := b5e41 X0
               grind)
            | exact superpose b5e41 b5e35
            | exact resolve b5e35 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e431 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op X4 (M.op (M.op (M.op X0 X1) X2) (M.op X2 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e35 (M.op X2 X2) X4 X3
               have i₂ := b5e32 X0 X1 X2 (M.op X2 X2)
               grind)
            | exact superpose b5e32 b5e35
            | exact resolve b5e35 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e448 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op X1 X1) x
               have i₂ := b5e35 X1 X0 x
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e469 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1))) = (M.op X2 (M.op (M.op X0 (M.op X1 (M.op X1 X1))) (M.op X1 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X1 (M.op X1 X1)) X3
               have i₂ := b5e35 X1 (M.op X1 (M.op X1 X1)) X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e470 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) ≠ (M.op (M.op X0 (M.op X1 (M.op X1 X1))) (M.op X1 X1)) ∨ (M.op X2 (M.op X1 (M.op X1 X1))) = (k (M.op X1 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 (M.op X1 (M.op X1 X1)) X2
               have i₂ := b5e35 X1 (M.op X1 (M.op X1 X1)) X0
               grind)
            | exact superpose b5e35 b5e16
            | (have j0 := b5e16 (M.op X1 (M.op X1 X1)) X2
               grind)
            | exact resolve b5e16 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e504 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X1)) ≠ (M.op (M.op y X1) (M.op X1 X1)) ∨ (M.op X2 (M.op X1 (M.op X1 X1))) = (k (M.op X1 (M.op X1 X1)) X2) := by
            intro X1 X2
            first
            | (have i₁ := b5e470 x X1 X2
               have i₂ := b5e385 X1 (M.op X1 X1) x
               grind)
            | exact superpose b5e385 b5e470
            | (have j0 := b5e470 x X1 X2
               grind)
            | exact resolve b5e470 b5e385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e470
          have b5e505 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1))) = (M.op X2 (M.op (M.op y X1) (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b5e469 x X1 X2 X3
               have i₂ := b5e385 X1 (M.op X1 X1) x
               grind)
            | exact superpose b5e385 b5e469
            | exact resolve b5e469 b5e385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e385 b5e469
          have b5e518 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e448 X0 X1
               have i₂ := b5e35 X1 X1 X1
               grind)
            | exact superpose b5e35 b5e448
            | exact resolve b5e448 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e448
          have b5e526 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op (M.op (M.op X0 X1) X2) (M.op X2 X2))) = (M.op (M.op X3 X4) (M.op X2 (M.op X2 (M.op X2 X2)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e431 X0 X1 X2 X3 X4
               have i₂ := b5e35 X2 X2 X2
               grind)
            | exact superpose b5e35 b5e431
            | exact resolve b5e431 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e431
          have b5e533 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X1 X1)) = (M.op (M.op y X0) (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e411 X0 X1
               have i₂ := b5e128 X0 X0 (M.op X1 (M.op X1 X1))
               grind)
            | exact superpose b5e128 b5e411
            | exact resolve b5e411 b5e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e128 b5e411
          have b5e547 : ∀ X1 X2 : G, (M.op X2 (M.op X1 (M.op X1 X1))) = (k (M.op X1 (M.op X1 X1)) X2) := by
            intro X1 X2
            first
            | (have j0 := b5e504 X1 X2
               grind)
            | (have r₁ := b5e504 X1 X2
               have r₂ := b5e351 X1 X1
               grind)
            | exact resolve b5e504 b5e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e504
          have b5e548 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X1 X1))) = (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b5e505 X1 X2 X3
               have i₂ := b5e351 X1 X1
               grind)
            | exact superpose b5e351 b5e505
            | exact resolve b5e505 b5e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e505
          have b5e551 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op (M.op (M.op X0 X1) X2) (M.op X2 X2))) = (M.op (M.op X3 X4) (M.op X2 (M.op X2 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e526 X0 X1 X2 X3 X4
               have i₂ := b5e518 (M.op X3 X4) X2
               grind)
            | exact superpose b5e518 b5e526
            | exact resolve b5e526 b5e518
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e518 b5e526
          have b5e553 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op y X0) (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e533 X0 X1
               have i₂ := b5e351 X0 X1
               grind)
            | exact superpose b5e351 b5e533
            | exact resolve b5e533 b5e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e351 b5e533
          have b5e559 : ∀ X0 X1 X2 X4 : G, (M.op X4 (M.op (M.op (M.op X0 X1) X2) (M.op X2 X2))) = (M.op X4 (M.op X2 (M.op X2 X2))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e551 X0 X1 X2 x X4
               have i₂ := b5e548 X2 X4 x
               grind)
            | exact superpose b5e548 b5e551
            | exact resolve b5e551 b5e548
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e551
          have b5e560 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e553 X0 X1
               have i₂ := b5e548 X1 X0 y
               grind)
            | exact superpose b5e548 b5e553
            | exact resolve b5e553 b5e548
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e553
          have b5e661 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 x X0
               have i₂ := b5e78 (σ X0)
               grind)
            | exact superpose b5e78 b5e19
            | (have j1 := b5e78 (σ X0)
               grind)
            | exact resolve b5e19 b5e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e814 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) (M.op X4 X4)) = (M.op X3 (M.op (M.op (M.op X4 (M.op X4 X4)) (M.op X4 (M.op X4 X4))) (M.op (M.op X4 (M.op X4 X4)) (M.op X4 (M.op X4 X4))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 X1 X2 X3 (M.op X4 (M.op X4 X4))
               have i₂ := b5e35 X4 (M.op X1 (M.op X2 X3)) X0
               grind)
            | exact superpose b5e35 b5e34
            | exact resolve b5e34 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e817 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X1 X1)) = (M.op X4 (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X1 X1)) X1))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 X0 X1 X2 (M.op X1 X1)
               have i₂ := b5e13 (M.op X1 X1) X1 X2
               grind)
            | exact superpose b5e13 b5e34
            | exact resolve b5e34 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e981 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X1 X1)) = (M.op X4 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b5e817 x X2 X2 X3 X4
               have i₂ := b5e33 x X2 X2
               grind)
            | exact superpose b5e33 b5e817
            | exact resolve b5e817 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e817
          have b5e983 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) (M.op X4 X4)) = (M.op X3 (M.op (M.op X4 (M.op X4 X4)) (M.op (M.op X4 (M.op X4 X4)) (M.op X4 (M.op X4 X4))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e814 X0 X1 X2 X3 X4
               have i₂ := b5e559 X4 (M.op X4 X4) (M.op X4 (M.op X4 X4)) X3
               grind)
            | exact superpose b5e559 b5e814
            | exact resolve b5e814 b5e559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e559 b5e814
          have b5e1069 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X1 X1)) = (M.op X4 (M.op (M.op X1 X1) (M.op X1 (M.op X1 X1)))) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b5e981 X1 X2 X3 X4
               have i₂ := b5e548 X1 (M.op X1 X1) X1
               grind)
            | exact superpose b5e548 b5e981
            | exact resolve b5e981 b5e548
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e981
          have b5e1071 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) (M.op X4 X4)) = (M.op X3 (M.op (M.op X4 (M.op X4 X4)) (M.op X4 (M.op X4 X4)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e983 X0 X1 X2 X3 X4
               have i₂ := b5e560 X3 (M.op X4 (M.op X4 X4))
               grind)
            | exact superpose b5e560 b5e983
            | exact resolve b5e983 b5e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e983
          have b5e1124 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X1 X1)) = (M.op X4 (M.op X1 (M.op X1 (M.op X1 X1)))) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b5e1069 X1 X2 X3 X4
               have i₂ := b5e548 X1 X1 X1
               grind)
            | exact superpose b5e548 b5e1069
            | exact resolve b5e1069 b5e548
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1069
          have b5e1126 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) (M.op X4 X4)) = (M.op X3 (M.op (M.op X4 X4) (M.op X4 (M.op X4 X4)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e1071 X0 X1 X2 X3 X4
               have i₂ := b5e548 X4 (M.op X4 X4) X4
               grind)
            | exact superpose b5e548 b5e1071
            | exact resolve b5e1071 b5e548
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1071
          have b5e1164 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X4)) (M.op X1 X1)) = (M.op X4 (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b5e1124 X1 X2 X3 X4
               have i₂ := b5e560 X1 X1
               grind)
            | exact superpose b5e560 b5e1124
            | exact resolve b5e1124 b5e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1124
          have b5e1166 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) (M.op X4 X4)) = (M.op X3 (M.op X4 (M.op X4 (M.op X4 X4)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e1126 X0 X1 X2 X3 X4
               have i₂ := b5e548 X4 X4 X4
               grind)
            | exact superpose b5e548 b5e1126
            | exact resolve b5e1126 b5e548
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1126
          have b5e1195 : ∀ X1 X2 X3 X4 : G, (M.op X4 (M.op X1 X1)) = (M.op (M.op X2 (M.op X3 X4)) (M.op X1 X1)) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b5e1164 X1 X2 X3 X4
               have i₂ := b5e560 X4 X1
               grind)
            | exact superpose b5e560 b5e1164
            | exact resolve b5e1164 b5e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1164
          have b5e1197 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) (M.op X4 X4)) = (M.op X3 (M.op X4 (M.op X4 X4))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e1166 X0 X1 X2 X3 X4
               have i₂ := b5e560 X4 X4
               grind)
            | exact superpose b5e560 b5e1166
            | exact resolve b5e1166 b5e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1166
          have b5e1211 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 X4)) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) (M.op X4 X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e1197 X0 X1 X2 X3 X4
               have i₂ := b5e560 X3 X4
               grind)
            | exact superpose b5e560 b5e1197
            | exact resolve b5e1197 b5e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1197
          have b5e1220 : ∀ X2 X3 X4 : G, (M.op X3 (M.op X4 X4)) = (M.op (M.op X2 X3) (M.op X4 X4)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e1211 x x X2 X3 X4
               have i₂ := b5e1195 X4 x x (M.op X2 X3)
               grind)
            | (have i₁ := b5e1211 x x X2 X3 x
               have i₂ := b5e1195 x X2 X3 (M.op x (M.op x (M.op X2 X3)))
               grind)
            | exact superpose b5e1195 b5e1211
            | exact resolve b5e1211 b5e1195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1195 b5e1211
          have b5e1326 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e79 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e1480 : ∀ X0 : G, (M.op y y) ≠ (M.op y y) ∨ (M.op X0 (M.op y y)) = (k (M.op y y) X0) := by
            intro X0
            first
            | (have i₁ := b5e43 y X0
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e43
            | (have j0 := b5e43 y X0
               grind)
            | (have r₁ := b5e43 y x
               have r₂ := b5e31 y
               grind)
            | exact resolve b5e43 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e1481 : ∀ X0 : G, (M.op X0 (M.op y y)) = (k (M.op y y) X0) := by
            intro X0
            first
            | (have j0 := b5e1480 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1480
          have b5e1575 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e56 X0 X0 (M.op X1 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e2636 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 (σ X0) X1
               have i₂ := b5e69 X0 X0
               grind)
            | exact superpose b5e69 b5e16
            | (have j0 := b5e16 (σ X0) X1
               have j1 := b5e69 X0 X0
               grind)
            | (have r₁ := b5e16 (σ X0) X1
               have r₂ := b5e69 X0 X1
               grind)
            | (have r₁ := b5e16 (σ X1) X1
               have r₂ := b5e69 X1 X1
               grind)
            | exact resolve b5e16 b5e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2658 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (σ X1)) X3) = (M.op (σ (k X0 X1)) X3) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e29 X2 (σ X1) X3 (σ X0)
               have i₂ := b5e69 X0 X1
               grind)
            | exact superpose b5e69 b5e29
            | (have j1 := b5e69 X0 X0
               grind)
            | exact resolve b5e29 b5e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2691 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e69 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e2693 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e2691 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2691
          have b5e2715 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e2636 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2636
          have b5e2727 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e2715 X0 X1
               have j1 := b5e16 (σ X0) X1
               grind)
            | (have r₁ := b5e2715 X0 X1
               have r₂ := b5e16 (σ X0) X1
               grind)
            | exact resolve b5e2715 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2715
          have b5e20355 : ∀ X0 X1 : G, (k (σ (M.op X1 (M.op X1 X1))) X0) = (σ (M.op (τ X0) (M.op X1 (M.op X1 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e27 X0 (M.op X1 (M.op X1 X1))
               have i₂ := b5e547 X1 (τ X0)
               grind)
            | exact superpose b5e547 b5e27
            | exact resolve b5e27 b5e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e20363 : ∀ X0 X1 : G, (σ (M.op (τ X0) (M.op X1 X1))) = (k (σ (M.op X1 (M.op X1 X1))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e20355 X0 X1
               have i₂ := b5e560 (τ X0) X1
               grind)
            | exact superpose b5e560 b5e20355
            | exact resolve b5e20355 b5e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20355
          have b5e26701 : (σ (M.op y y)) ≠ (σ (M.op (M.op y y) (M.op y y))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e2693 (M.op y y)
               have i₂ := b5e1481 (M.op y y)
               grind)
            | exact superpose b5e1481 b5e2693
            | (have j0 := b5e2693 (M.op y y)
               grind)
            | exact resolve b5e2693 b5e1481
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2693
          have b5e26719 : (σ (M.op y y)) ≠ (σ (M.op y (M.op y (M.op y y)))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e26701
               have i₂ := b5e35 y y y
               grind)
            | exact superpose b5e35 b5e26701
            | exact resolve b5e26701 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26701
          have b5e26726 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e26719
               have i₂ := b5e41 y
               grind)
            | (have i₁ := b5e26719
               have i₂ := b5e41 (M.op y (M.op y y))
               grind)
            | exact superpose b5e41 b5e26719
            | exact resolve b5e26719 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26719
          have b5e26727 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
          clear b5e26726
          have b5e27157 : ∀ X0 : G, (σ (M.op y y)) ≠ (σ (M.op (M.op y y) (M.op y y))) ∨ (k (σ (M.op y y)) X0) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b5e2727 (M.op y y) X0
               have i₂ := b5e1481 (M.op y y)
               grind)
            | exact superpose b5e1481 b5e2727
            | (have j0 := b5e2727 (M.op y y) X0
               grind)
            | exact resolve b5e2727 b5e1481
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e27161 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) ∨ (k (σ (M.op X0 (M.op X0 X0))) X1) = (M.op X1 (σ (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2727 (M.op X0 (M.op X0 X0)) X1
               have i₂ := b5e547 X0 (M.op X0 (M.op X0 X0))
               grind)
            | exact superpose b5e547 b5e2727
            | (have j0 := b5e2727 (M.op X0 (M.op X0 X0)) X1
               grind)
            | exact resolve b5e2727 b5e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e547 b5e2727
          have b5e27172 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (σ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) ∨ (k (σ (M.op X0 (M.op X0 X0))) X1) = (M.op X1 (σ (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e27161 X0 X1
               have i₂ := b5e548 X0 (M.op X0 X0) X0
               grind)
            | exact superpose b5e548 b5e27161
            | (have j0 := b5e27161 X0 X1
               grind)
            | exact resolve b5e27161 b5e548
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27161
          have b5e27175 : ∀ X0 : G, (σ (M.op y y)) ≠ (σ (M.op y (M.op y (M.op y y)))) ∨ (k (σ (M.op y y)) X0) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b5e27157 X0
               have i₂ := b5e35 y y y
               grind)
            | exact superpose b5e35 b5e27157
            | (have j0 := b5e27157 X0
               grind)
            | exact resolve b5e27157 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e27157
          have b5e27180 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (σ (M.op X0 (M.op X0 (M.op X0 X0)))) ∨ (k (σ (M.op X0 (M.op X0 X0))) X1) = (M.op X1 (σ (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e27172 X0 X1
               have i₂ := b5e548 X0 X0 X0
               grind)
            | exact superpose b5e548 b5e27172
            | (have j0 := b5e27172 X0 X1
               grind)
            | exact resolve b5e27172 b5e548
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e548 b5e27172
          have b5e27183 : ∀ X0 : G, (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (k (σ (M.op y y)) X0) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b5e27175 X0
               have i₂ := b5e41 y
               grind)
            | (have i₁ := b5e27175 X0
               have i₂ := b5e41 (M.op y (M.op y y))
               grind)
            | exact superpose b5e41 b5e27175
            | (have j0 := b5e27175 X0
               grind)
            | exact resolve b5e27175 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e27175
          have b5e27184 : ∀ X0 : G, (k (σ (M.op y y)) X0) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have j0 := b5e27183 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27183
          have b5e27186 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (k (σ (M.op X0 (M.op X0 X0))) X1) = (M.op X1 (σ (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e27180 X0 X1
               have i₂ := b5e560 X0 X0
               grind)
            | exact superpose b5e560 b5e27180
            | (have j0 := b5e27180 X0 X1
               grind)
            | exact resolve b5e27180 b5e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e560 b5e27180
          have b5e27187 : ∀ X0 X1 : G, (k (σ (M.op X0 (M.op X0 X0))) X1) = (M.op X1 (σ (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have j0 := b5e27186 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27186
          have b5e27190 : ∀ X0 X1 : G, (σ (M.op (τ X1) (M.op X0 X0))) = (M.op X1 (σ (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e27187 X0 X1
               have i₂ := b5e20363 X1 X0
               grind)
            | exact superpose b5e20363 b5e27187
            | exact resolve b5e27187 b5e20363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20363 b5e27187
          have b5e28863 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (τ (M.op X0 (σ (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b5e95 (M.op y y) X0
               have i₂ := b5e27184 X0
               grind)
            | exact superpose b5e27184 b5e95
            | exact resolve b5e95 b5e27184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95 b5e27184
          have b5e28888 : ∀ X0 : G, (M.op (τ X0) (M.op y y)) = (τ (M.op X0 (σ (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b5e28863 X0
               have i₂ := b5e1481 (τ X0)
               grind)
            | exact superpose b5e1481 b5e28863
            | exact resolve b5e28863 b5e1481
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1481 b5e28863
          have b5e74502 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e1326 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1326
          have b5e74503 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e74502 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e74502 X0
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e74502 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74502
          have b5e74927 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e74503 (σ X0)
               grind)
            | exact superpose b5e74503 b5e19
            | exact resolve b5e19 b5e74503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e74946 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e74927 X0
               have i₂ := b5e74503 X0
               grind)
            | exact superpose b5e74503 b5e74927
            | exact resolve b5e74927 b5e74503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74503 b5e74927
          have b5e76258 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 (σ X0) X2
               have i₂ := b5e74946 X0
               grind)
            | exact superpose b5e74946 b5e13
            | exact resolve b5e13 b5e74946
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e76261 : ∀ X0 : G, (M.op y (σ X0)) = (M.op y (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e31 (σ X0)
               have i₂ := b5e74946 X0
               grind)
            | exact superpose b5e74946 b5e31
            | exact resolve b5e31 b5e74946
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e76319 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (M.op X2 X1) (σ (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1220 X2 x (σ X0)
               have i₂ := b5e74946 X0
               grind)
            | exact superpose b5e74946 b5e1220
            | exact resolve b5e1220 b5e74946
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e125998 : ∀ X0 X1 : G, (M.op (M.op y (σ X0)) (σ X1)) = (M.op (σ (M.op X0 X0)) (σ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e76258 X1 (σ (M.op X0 X0)) y
               have i₂ := b5e76261 X0
               grind)
            | exact superpose b5e76261 b5e76258
            | exact resolve b5e76258 b5e76261
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76261
          have b5e126102 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ (M.op X0 X0))) = (M.op X2 (σ (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e76258 (M.op X0 X0) X2 X1
               have i₂ := b5e1220 X0 X0 X0
               grind)
            | exact superpose b5e1220 b5e76258
            | exact resolve b5e76258 b5e1220
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76258
          have b5e127099 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ (M.op X0 X0))) = (σ (M.op (τ X2) (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e126102 X0 X1 X2
               have i₂ := b5e27190 X0 X2
               grind)
            | exact superpose b5e27190 b5e126102
            | exact resolve b5e126102 b5e27190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27190 b5e126102
          have b5e127571 : ∀ X0 X2 : G, (M.op X2 (σ (M.op X0 X0))) = (σ (M.op (τ X2) (M.op X0 X0))) := by
            intro X0 X2
            first
            | (have i₁ := b5e127099 X0 x X2
               have i₂ := b5e76319 X0 X2 x
               grind)
            | exact superpose b5e76319 b5e127099
            | exact resolve b5e127099 b5e76319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e127099
          have b5e248752 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op y y))) (σ (M.op X1 X1))) = (σ (M.op (M.op (τ X0) (M.op y y)) (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e127571 X1 (M.op X0 (σ (M.op y y)))
               have i₂ := b5e28888 X0
               grind)
            | exact superpose b5e28888 b5e127571
            | exact resolve b5e127571 b5e28888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28888 b5e127571
          have b5e249046 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op y y))) (σ (M.op X1 X1))) = (σ (M.op (M.op y y) (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e248752 X0 X1
               have i₂ := b5e1220 (τ X0) (M.op y y) X1
               grind)
            | (have i₁ := b5e248752 X0 x
               have i₂ := b5e1220 x (M.op (τ X0) (M.op y y)) x
               grind)
            | exact superpose b5e1220 b5e248752
            | exact resolve b5e248752 b5e1220
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248752
          have b5e249111 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op y y))) (σ (M.op X1 X1))) = (σ (M.op y (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e249046 X0 X1
               have i₂ := b5e1220 y y X1
               grind)
            | (have i₁ := b5e249046 X0 x
               have i₂ := b5e1220 x (M.op y y) x
               grind)
            | exact superpose b5e1220 b5e249046
            | exact resolve b5e249046 b5e1220
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1220 b5e249046
          have b5e249141 : ∀ X0 X1 : G, (σ (M.op y X1)) = (M.op (M.op X0 (σ (M.op y y))) (σ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e249111 X0 X1
               have i₂ := b5e31 X1
               grind)
            | exact superpose b5e31 b5e249111
            | exact resolve b5e249111 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e249111
          have b5e249156 : ∀ X1 : G, (M.op (σ (M.op y y)) (σ (M.op X1 X1))) = (σ (M.op y X1)) := by
            intro X1
            first
            | (have i₁ := b5e249141 x X1
               have i₂ := b5e76319 X1 (σ (M.op y y)) x
               grind)
            | exact superpose b5e76319 b5e249141
            | exact resolve b5e249141 b5e76319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76319 b5e249141
          have b5e249162 : ∀ X1 : G, (σ (M.op y X1)) = (M.op (M.op y (σ y)) (σ X1)) := by
            intro X1
            first
            | (have i₁ := b5e249156 X1
               have i₂ := b5e125998 y X1
               grind)
            | exact superpose b5e125998 b5e249156
            | exact resolve b5e249156 b5e125998
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e125998 b5e249156
          have b5e250125 : ∀ X0 X1 : G, (σ (M.op y X0)) = (M.op (M.op X1 (σ y)) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 X1 (σ y) (σ X0) y
               have i₂ := b5e249162 X0
               grind)
            | exact superpose b5e249162 b5e29
            | exact resolve b5e29 b5e249162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29 b5e249162
          have b5e258939 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ (k x y)) (σ X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e250125 X0 (σ x)
               have i₂ := b5e661 y
               grind)
            | exact superpose b5e661 b5e250125
            | (have j1 := b5e661 y
               grind)
            | exact resolve b5e250125 b5e661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e250125
          have b5e259339 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ (k x y)) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e258939 X0
               grind)
            | (have r₁ := b5e258939 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e258939 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e258939
          have b5e259464 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e259339 X0
               have i₂ := b5e62
               grind)
            | exact superpose b5e62 b5e259339
            | exact resolve b5e259339 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e259339
          have b5e261978 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op y (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e259464 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e259464
            | exact resolve b5e259464 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e262004 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e259464 y
               grind)
            | exact superpose b5e259464 b5e24
            | exact resolve b5e24 b5e259464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e262006 : (σ (M.op x x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b5e74946 x
               have i₂ := b5e259464 x
               grind)
            | exact superpose b5e259464 b5e74946
            | exact resolve b5e74946 b5e259464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e266794 : ∀ X0 : G, (σ (k X0 (M.op y x))) = (k (σ X0) (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 (M.op y x)
               have i₂ := b5e262006
               grind)
            | exact superpose b5e262006 b5e19
            | exact resolve b5e19 b5e262006
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e262006
          have b5e266849 : ∀ X0 : G, (σ (k X0 (M.op y x))) = (σ (k X0 (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b5e266794 X0
               have i₂ := b5e19 X0 (M.op x x)
               grind)
            | exact superpose b5e19 b5e266794
            | exact resolve b5e266794 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e266794
          have b5e277984 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ y)) X1) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e2658 x y X0 X1
               have i₂ := b5e62
               grind)
            | exact superpose b5e62 b5e2658
            | (have j0 := b5e2658 x x x x
               grind)
            | exact resolve b5e2658 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2658
          have b5e279312 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ y)) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b5e277984 X0 X1
               grind)
            | (have r₁ := b5e277984 X0 X1
               have r₂ := b5e23
               grind)
            | exact resolve b5e277984 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e277984
          have b5e279615 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ y)) X1) := by
            intro X0 X1
            first
            | (have j0 := b5e279312 X0 X1
               grind)
            | (have r₁ := b5e279312 X0 X1
               have r₂ := b5e24
               grind)
            | exact resolve b5e279312 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e279312
          have b5e280119 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ x) X0)) = (σ (k X1 (M.op y (τ X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 (M.op y (τ X0))
               have i₂ := b5e261978 X0
               grind)
            | exact superpose b5e261978 b5e19
            | exact resolve b5e19 b5e261978
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e261978
          have b5e292914 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (σ x) (M.op X0 (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e1575 (σ y) X0
               have i₂ := b5e279615 X0 (M.op X0 (σ y))
               grind)
            | exact superpose b5e279615 b5e1575
            | (have j0 := b5e1575 (σ y) x
               grind)
            | exact resolve b5e1575 b5e279615
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1575 b5e279615
          have b5e293394 : ∀ X0 : G, (σ y) = (σ (k y (M.op y (τ (M.op X0 (σ y)))))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e292914 X0
               have i₂ := b5e280119 (M.op X0 (σ y)) y
               grind)
            | exact superpose b5e280119 b5e292914
            | exact resolve b5e292914 b5e280119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e280119 b5e292914
          have b5e293661 : ∀ X0 : G, (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (k y (M.op y (τ (M.op X0 (σ y)))))) := by
            intro X0
            first
            | (have i₁ := b5e293394 X0
               have i₂ := b5e74946 y
               grind)
            | exact superpose b5e74946 b5e293394
            | (have j0 := b5e293394 X0
               grind)
            | exact resolve b5e293394 b5e74946
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74946 b5e293394
          have b5e293853 : ∀ X0 : G, (σ y) = (σ (k y (M.op y (τ (M.op X0 (σ y)))))) := by
            intro X0
            first
            | (have j0 := b5e293661 X0
               grind)
            | (have r₁ := b5e293661 X0
               have r₂ := b5e262004
               grind)
            | exact resolve b5e293661 b5e262004
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e262004 b5e293661
          have b5e333459 : (σ y) = (σ (k y (M.op y (τ (σ (k x y)))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e293853 (σ x)
               have i₂ := b5e661 y
               grind)
            | exact superpose b5e661 b5e293853
            | (have j1 := b5e661 y
               grind)
            | exact resolve b5e293853 b5e661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e293853
          have b5e333554 : (σ y) = (σ (k y (M.op y (τ (σ (k x y)))))) := by
            first
            | (have r₁ := b5e333459
               have r₂ := b5e24
               grind)
            | exact resolve b5e333459 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e333459
          have b5e333599 : (σ y) = (σ (k y (M.op y (k x y)))) := by
            first
            | (have i₁ := b5e333554
               have i₂ := b5e14 (k x y)
               grind)
            | exact superpose b5e14 b5e333554
            | exact resolve b5e333554 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e333554
          have b5e333625 : (σ y) = (σ (k y (M.op y x))) := by
            first
            | (have i₁ := b5e333599
               have i₂ := b5e62
               grind)
            | exact superpose b5e62 b5e333599
            | exact resolve b5e333599 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e333599
          have b5e333631 : (σ y) = (σ (k y (M.op x x))) := by
            first
            | (have i₁ := b5e333625
               have i₂ := b5e266849 y
               grind)
            | exact superpose b5e266849 b5e333625
            | exact resolve b5e333625 b5e266849
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e266849 b5e333625
          have b5e334208 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (k y (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 (k y (M.op x x))
               have i₂ := b5e333631
               grind)
            | exact superpose b5e333631 b5e19
            | exact resolve b5e19 b5e333631
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e334223 : (M.op (σ x) (σ y)) = (σ (k x (k y (M.op x x)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e661 (k y (M.op x x))
               have i₂ := b5e333631
               grind)
            | exact superpose b5e333631 b5e661
            | (have j0 := b5e661 y
               grind)
            | exact resolve b5e661 b5e333631
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e661 b5e333631
          have b5e334250 : (M.op (σ x) (σ y)) = (σ (k x (k y (M.op x x)))) := by
            first
            | (have r₁ := b5e334223
               have r₂ := b5e24
               grind)
            | exact resolve b5e334223 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e334223
          have b5e334265 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (k y (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b5e334208 X0
               have i₂ := b5e19 X0 y
               grind)
            | exact superpose b5e19 b5e334208
            | exact resolve b5e334208 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e334208
          have b5e334279 : (σ (M.op y y)) = (σ (k x (k y (M.op x x)))) := by
            first
            | (have i₁ := b5e334250
               have i₂ := b5e259464 y
               grind)
            | exact superpose b5e259464 b5e334250
            | exact resolve b5e334250 b5e259464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e259464 b5e334250
          have b5e334287 : (σ (M.op y y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e334279
               have i₂ := b5e334265 x
               grind)
            | exact superpose b5e334265 b5e334279
            | exact resolve b5e334279 b5e334265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e334265 b5e334279
          have b5e334291 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e334287
               have i₂ := b5e62
               grind)
            | exact superpose b5e62 b5e334287
            | exact resolve b5e334287 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62 b5e334287
          have b5e334750 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e26727
               have i₂ := b5e334291
               grind)
            | exact superpose b5e334291 b5e26727
            | exact resolve b5e26727 b5e334291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26727 b5e334291
          have b5e334827 : False := by grind
          exact b5e334827
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
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
        have b6e40 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e38 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e43 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e40 (σ X0)
             grind)
          | exact superpose b6e40 b6e18
          | exact resolve b6e18 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e96 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e43 x
             grind)
          | exact superpose b6e43 b6e22
          | exact resolve b6e22 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e163 : (τ (σ x)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e96
             grind)
          | exact superpose b6e96 b6e13
          | exact resolve b6e13 b6e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e96
        have b6e165 : x = (k x x) := by
          first
          | (have i₁ := b6e163
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e163
          | exact resolve b6e163 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e163
        have b6e187 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e165
             grind)
          | exact superpose b6e165 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e165
        have b6e188 : x = (M.op x x) := by grind
        clear b6e187
        have b6e190 : False := by grind
        exact b6e190
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
          have b7e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op X1 X1) X3
               have i₂ := b7e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X2 X3
               have i₂ := b7e13 X1 X2 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X2 X2) X3 X1
               have i₂ := b7e13 X1 X2 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 (M.op x X0)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b7e32 x X1 X2 X3
               have i₂ := b7e37 x X1 X1
               grind)
            | exact superpose b7e37 b7e32
            | exact resolve b7e32 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e58 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e61 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e58
          have b7e62 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e23
               grind)
            | exact resolve b7e61 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
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
          have b7e92 : x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e93 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e92
               have r₂ := b7e21
               grind)
            | exact resolve b7e92 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e95 : x = (M.op x y) := by
            first
            | (have r₁ := b7e93
               have r₂ := b7e22
               grind)
            | exact resolve b7e93 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e136 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 x y X0 X1
               have i₂ := b7e95
               grind)
            | exact superpose b7e95 b7e33
            | exact resolve b7e33 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e138 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 x
               have i₂ := b7e95
               grind)
            | exact superpose b7e95 b7e13
            | exact resolve b7e13 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e321 : ∀ X0 : G, (M.op y (M.op X0 (M.op X0 X0))) = (M.op x (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e39 X0 y x
               have i₂ := b7e95
               grind)
            | exact superpose b7e95 b7e39
            | exact resolve b7e39 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e354 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (M.op X1 X1) x
               have i₂ := b7e39 X1 X0 x
               grind)
            | exact superpose b7e39 b7e13
            | exact resolve b7e13 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e357 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 (M.op X1 X1))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e37 (M.op x X0) X1 X2
               have i₂ := b7e39 X1 X0 x
               grind)
            | exact superpose b7e39 b7e37
            | exact resolve b7e37 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e400 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e354 X0 X1
               have i₂ := b7e39 X1 X1 X1
               grind)
            | exact superpose b7e39 b7e354
            | exact resolve b7e354 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e354
          have b7e436 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e36 x x y X0
               have i₂ := b7e136 X0 (M.op x x)
               grind)
            | exact superpose b7e136 b7e36
            | exact resolve b7e36 b7e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e463 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e436 X0
               have i₂ := b7e136 (M.op X0 X0) y
               grind)
            | exact superpose b7e136 b7e436
            | exact resolve b7e436 b7e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e136 b7e436
          have b7e480 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op X1 X1))) = (M.op y (M.op (M.op X0 (M.op X1 (M.op X1 X1))) (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e138 (M.op X1 (M.op X1 X1))
               have i₂ := b7e39 X1 (M.op X1 (M.op X1 X1)) X0
               grind)
            | exact superpose b7e39 b7e138
            | exact resolve b7e138 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e500 : ∀ X1 : G, (M.op x (M.op X1 (M.op X1 X1))) = (M.op y (M.op X1 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
            intro X1
            first
            | (have i₁ := b7e480 x X1
               have i₂ := b7e357 x X1 (M.op X1 X1)
               grind)
            | exact superpose b7e357 b7e480
            | exact resolve b7e480 b7e357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e357 b7e480
          have b7e502 : ∀ X1 : G, (M.op x (M.op X1 (M.op X1 X1))) = (M.op y (M.op X1 (M.op X1 (M.op X1 (M.op X1 X1))))) := by
            intro X1
            first
            | (have i₁ := b7e500 X1
               have i₂ := b7e39 X1 X1 X1
               grind)
            | exact superpose b7e39 b7e500
            | exact resolve b7e500 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e500
          have b7e503 : ∀ X1 : G, (M.op x (M.op X1 (M.op X1 X1))) = (M.op y (M.op X1 (M.op X1 (M.op X1 X1)))) := by
            intro X1
            first
            | (have i₁ := b7e502 X1
               have i₂ := b7e400 X1 X1
               grind)
            | exact superpose b7e400 b7e502
            | exact resolve b7e502 b7e400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e502
          have b7e504 : ∀ X1 : G, (M.op x (M.op X1 (M.op X1 X1))) = (M.op y (M.op X1 (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b7e503 X1
               have i₂ := b7e400 y X1
               grind)
            | exact superpose b7e400 b7e503
            | exact resolve b7e503 b7e400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e400 b7e503
          have b7e505 : ∀ X1 : G, (M.op x (M.op X1 X1)) = (M.op x (M.op X1 (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b7e504 X1
               have i₂ := b7e321 X1
               grind)
            | exact superpose b7e321 b7e504
            | exact resolve b7e504 b7e321
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e321 b7e504
          have b7e506 : ∀ X1 : G, (M.op x X1) = (M.op x (M.op X1 (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b7e505 X1
               have i₂ := b7e463 X1
               grind)
            | exact superpose b7e463 b7e505
            | exact resolve b7e505 b7e463
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e463 b7e505
          have b7e1785 : (M.op x y) = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b7e506 y
               have i₂ := b7e138 y
               grind)
            | exact superpose b7e138 b7e506
            | exact resolve b7e506 b7e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e138 b7e506
          have b7e1806 : x = (M.op x x) := by
            first
            | (have i₁ := b7e1785
               have i₂ := b7e95
               grind)
            | exact superpose b7e95 b7e1785
            | exact resolve b7e1785 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95 b7e1785
          have b7e1823 : False := by grind
          exact b7e1823
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X0) (σ X0)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3174 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e72 x y
               grind)
            | exact superpose b8e72 b8e20
            | (have j1 := b8e72 x x
               grind)
            | exact resolve b8e20 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e3285 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e3174
               have r₂ := b8e23
               grind)
            | exact resolve b8e3174 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3174
          have b8e3291 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e3285
               have r₂ := b8e24
               grind)
            | exact resolve b8e3285 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3285
          have b8e3295 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e3291
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e3291
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e3291 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3291
          have b8e3296 : x = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e3295
          have b8e3298 : y = (M.op x y) := by
            first
            | (have r₁ := b8e3296
               have r₂ := b8e21
               grind)
            | exact resolve b8e3296 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3296
          have b8e3300 : False := by grind
          exact b8e3300

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4502 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4502 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
        intro X0 X1 X2 X3
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
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e33 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X2 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e11 X3 (M.op X2 X2) X4 X5
           have i₂ := b0e11 (M.op X2 X2) X2 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ x)) = (M.op X0 (σ y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 (σ x) X1 X2
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) x) = (M.op X0 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 x X1 X2
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (M.op (M.op X2 X2) (M.op X2 X2))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X3 (M.op X2 X2) x x
           have i₂ := b0e11 (M.op x x) X2 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
        intro X1
        first
        | (have i₁ := b0e40 x X1
           have i₂ := b0e41 x X1
           grind)
        | exact superpose b0e41 b0e40
        | exact resolve b0e40 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e46 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op y X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e33 X0 X1 X2 X3 x x
           have i₂ := b0e41 (M.op x x) X2
           grind)
        | exact superpose b0e41 b0e33
        | exact resolve b0e33 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e65 : ∀ X0 : G, (M.op X0 y) = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b0e35 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e66 : ∀ X0 X3 : G, (M.op X0 y) = (M.op X3 y) := by
        intro X0 X3
        first
        | (have i₁ := b0e35 X3 x x
           have i₂ := b0e35 X0 x x
           grind)
        | exact superpose b0e35 b0e35
        | exact resolve b0e35 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b0e90 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X3 X4) X2) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X1 X2 X3 X4
           have i₂ := b0e16 X2 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2 X3
           have i₂ := b0e16 X0 (M.op X1 X1)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X2 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e95 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) ∨ (M.op (M.op X2 X3) X1) = X0 ∨ (M.op (M.op X1 X1) X0) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X1 X1) X1 X2 X3
           have i₂ := b0e16 (M.op X1 X1) X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2 X3
           have i₂ := b0e16 X0 (M.op X0 (M.op X1 X1))
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 (M.op X1 X1) X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e96 : ∀ X0 X1 X2 X3 : G, (k (M.op X2 X3) X0) = (M.op (M.op X2 X3) X0) ∨ (M.op X1 X0) = X0 ∨ (M.op (M.op X2 X3) X0) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 (M.op X2 X3) X2 X3
           have i₂ := b0e16 (M.op X2 X3) X1
           grind)
        | (have i₁ := b0e11 X0 X1 X2 X3
           have i₂ := b0e16 X0 (M.op (M.op X2 X3) X1)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 (M.op X2 X3) X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e126 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op y X2) = (M.op X1 X0) ∨ (M.op X2 X0) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e41 X1 X2
           have i₂ := b0e16 X2 X0
           grind)
        | (have i₁ := b0e41 X0 X1
           have i₂ := b0e16 X0 (M.op X1 X1)
           grind)
        | exact superpose b0e16 b0e41
        | (have j1 := b0e16 X2 X0
           grind)
        | exact resolve b0e41 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e127 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e41 X0 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e41
        | exact resolve b0e41 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e134 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op X2 X3) X0) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e11 x X0 X2 X3
           have i₂ := b0e41 x X0
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e136 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 (M.op X0 X0) X2 X3
           have i₂ := b0e41 (M.op X0 X0) X0
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e144 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e136 X0 X1 x x
           have i₂ := b0e41 (M.op x x) X0
           grind)
        | exact superpose b0e41 b0e136
        | exact resolve b0e136 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136
      have b0e192 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k X0 (τ X1))
           have i₂ := b0e26 X1 X0
           grind)
        | exact superpose b0e26 b0e12
        | exact resolve b0e12 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e213 : ∀ X0 X3 : G, (M.op X0 (σ y)) = (M.op X3 (σ y)) := by
        intro X0 X3
        first
        | (have i₁ := b0e34 X3 x x
           have i₂ := b0e34 X0 x x
           grind)
        | exact superpose b0e34 b0e34
        | exact resolve b0e34 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e626 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) (M.op y X0)) := by
        intro X0 X1 X2
        grind
      have b0e628 : ∀ X0 X1 X2 X3 : G, (M.op y X0) ≠ (M.op (M.op X2 X3) X0) ∨ (M.op X1 X1) = (M.op (M.op X2 X3) X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e15 X1 (M.op (M.op X2 X3) X0)
           have i₂ := b0e46 X2 X3 X0 X1
           grind)
        | exact superpose b0e46 b0e15
        | (have j0 := b0e15 X1 (M.op (M.op X2 X3) X0)
           grind)
        | exact resolve b0e15 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e640 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X2 X3) X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e628 X0 X1 X2 X3
           grind)
        | (have r₁ := b0e628 X0 X1 X2 X3
           have r₂ := b0e134 X0 X2 X3
           grind)
        | exact resolve b0e628 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e628
      have b0e641 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e626 X0 x x
           have i₂ := b0e134 X0 x x
           grind)
        | exact superpose b0e134 b0e626
        | exact resolve b0e626 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e626
      have b0e661 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op y X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e640 X0 X1 X2 X3
           have i₂ := b0e134 X0 X2 X3
           grind)
        | exact superpose b0e134 b0e640
        | (have j0 := b0e640 X0 X1 X2 X3
           grind)
        | exact resolve b0e640 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e640
      have b0e666 : ∀ X0 X1 : G, (k X1 (M.op y X0)) = X1 ∨ (M.op X1 X1) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e661 X0 X1 x x
           have i₂ := b0e134 X0 x x
           grind)
        | exact superpose b0e134 b0e661
        | (have j0 := b0e661 X0 X1 x x
           grind)
        | exact resolve b0e661 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e661
      have b0e905 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e213 (σ x) X0
           grind)
        | (have i₁ := b0e18
           have i₂ := b0e213 X0 (σ x)
           grind)
        | exact superpose b0e213 b0e18
        | exact resolve b0e18 b0e213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e213
      have b0e1862 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e90 X1 X1 X0 X3 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1863 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e90 (M.op X0 X1) X1 (M.op X0 X1) x x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90
      have b0e1864 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e1863 X0 X1 x
           have j1 := b0e96 (M.op X0 X1) (M.op X0 X1) X0 X1
           grind)
        | (have r₁ := b0e1863 X0 X1 X1
           have r₂ := b0e96 (M.op X0 X1) X1 x x
           grind)
        | (have r₁ := b0e1863 X0 X1 (M.op x x)
           have r₂ := b0e96 (M.op X0 X1) X1 x x
           grind)
        | exact resolve b0e1863 b0e96
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1863
      have b0e1865 : ∀ X0 X1 : G, (M.op y X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1862 X0 X1 x x
           have i₂ := b0e134 X0 x x
           grind)
        | exact superpose b0e134 b0e1862
        | (have j0 := b0e1862 X0 X1 x x
           grind)
        | (have r₁ := b0e1862 X0 (M.op y X0) x x
           have r₂ := b0e134 X0 x x
           grind)
        | exact resolve b0e1862 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1862
      have b0e1958 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1864 X0 X1
           have i₂ := b0e134 (M.op X0 X1) X0 X1
           grind)
        | exact superpose b0e134 b0e1864
        | (have j0 := b0e1864 X0 X1
           grind)
        | exact resolve b0e1864 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1864
      have b0e2016 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op y (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1958 X0 X1
           have i₂ := b0e134 (M.op X0 X1) X0 X1
           grind)
        | exact superpose b0e134 b0e1958
        | (have j0 := b0e1958 X0 X1
           grind)
        | exact resolve b0e1958 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1958
      have b0e2229 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ (σ (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e905 X1
           have i₂ := b0e66 x X0
           grind)
        | (have i₁ := b0e905 X1
           have i₂ := b0e66 X0 x
           grind)
        | exact superpose b0e66 b0e905
        | exact resolve b0e905 b0e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e905
      have b0e2339 : ∀ X0 X1 : G, (M.op y X0) = (k y X0) ∨ (M.op X1 X0) = X0 ∨ (M.op y X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e96 X0 X1 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e96
        | (have j0 := b0e96 X0 X1 x x
           grind)
        | exact resolve b0e96 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2411 : ∀ X1 X2 : G, y = (M.op y x) ∨ (M.op (M.op X1 X2) y) = (k (M.op X1 X2) y) ∨ y = (M.op (M.op X1 X2) y) := by
        intro X1 X2
        first
        | (have i₁ := b0e65 x
           have i₂ := b0e96 y x X1 X2
           grind)
        | exact superpose b0e96 b0e65
        | (have j1 := b0e96 y (M.op X1 X2) X1 X2
           grind)
        | exact resolve b0e65 b0e96
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e96
      have b0e2440 : ∀ X1 X2 : G, (M.op y x) = (k (M.op X1 X2) y) ∨ y = (M.op y x) ∨ y = (M.op (M.op X1 X2) y) := by
        intro X1 X2
        first
        | (have i₁ := b0e2411 X1 X2
           have i₂ := b0e65 (M.op X1 X2)
           grind)
        | exact superpose b0e65 b0e2411
        | (have j0 := b0e2411 X1 X2
           grind)
        | exact resolve b0e2411 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2411
      have b0e2480 : ∀ X1 X2 : G, y = (M.op y x) ∨ (M.op y x) = (k (M.op X1 X2) y) ∨ y = (M.op y x) := by
        intro X1 X2
        first
        | (have i₁ := b0e2440 X1 X2
           have i₂ := b0e65 (M.op X1 X2)
           grind)
        | exact superpose b0e65 b0e2440
        | (have j0 := b0e2440 X1 X2
           grind)
        | exact resolve b0e2440 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2440
      have b0e2481 : ∀ X1 X2 : G, (M.op y x) = (k (M.op X1 X2) y) ∨ y = (M.op y x) := by
        intro X1 X2
        first
        | (have j0 := b0e2480 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2480
      have b0e2536 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b0e2229 x X0
           have i₂ := b0e65 x
           grind)
        | exact superpose b0e65 b0e2229
        | exact resolve b0e2229 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2668 : ∀ X0 X3 X4 : G, (M.op X4 (M.op (M.op X3 X3) (M.op X3 X3))) = X0 ∨ (k (M.op X3 X3) X0) = (M.op (M.op X3 X3) X0) ∨ (M.op (M.op X3 X3) X0) = X0 := by
        intro X0 X3 X4
        first
        | (have i₁ := b0e43 x x X3 X4
           have i₂ := b0e95 X0 X3 x x
           grind)
        | (have i₁ := b0e43 X0 x x X3
           have i₂ := b0e95 (M.op (M.op X0 x) x) x x X3
           grind)
        | exact superpose b0e95 b0e43
        | (have j1 := b0e95 X0 X3 x X3
           grind)
        | exact resolve b0e43 b0e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e95
      have b0e2755 : ∀ X0 X3 : G, (M.op y (M.op X3 X3)) = X0 ∨ (k (M.op X3 X3) X0) = (M.op (M.op X3 X3) X0) ∨ (M.op (M.op X3 X3) X0) = X0 := by
        intro X0 X3
        first
        | (have i₁ := b0e2668 X0 X3 x
           have i₂ := b0e41 x (M.op X3 X3)
           grind)
        | exact superpose b0e41 b0e2668
        | (have j0 := b0e2668 X0 X3 x
           grind)
        | exact resolve b0e2668 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2668
      have b0e2848 : ∀ X0 X3 : G, (k (M.op X3 X3) X0) = (M.op (M.op X3 X3) X0) ∨ (M.op (M.op X3 X3) X0) = X0 := by
        intro X0 X3
        first
        | (have j0 := b0e2755 X0 X3
           have j1 := b0e1865 (M.op X3 X3) X0
           grind)
        | (have r₁ := b0e2755 x X3
           have r₂ := b0e1865 (M.op X3 X3) x
           grind)
        | (have r₁ := b0e2755 (M.op y X0) X3
           have r₂ := b0e1865 X0 (M.op y (M.op X3 X3))
           grind)
        | (have r₁ := b0e2755 (M.op y X0) X3
           have r₂ := b0e1865 X0 (M.op (M.op X3 X3) (M.op y X0))
           grind)
        | exact resolve b0e2755 b0e1865
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1865 b0e2755
      have b0e2930 : ∀ X0 X3 : G, (M.op y X0) = (k (M.op X3 X3) X0) ∨ (M.op (M.op X3 X3) X0) = X0 := by
        intro X0 X3
        first
        | (have i₁ := b0e2848 X0 X3
           have i₂ := b0e134 X0 X3 X3
           grind)
        | exact superpose b0e134 b0e2848
        | (have j0 := b0e2848 X0 X3
           grind)
        | exact resolve b0e2848 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2848
      have b0e2993 : ∀ X0 X3 : G, (M.op y X0) = (k (M.op X3 X3) X0) ∨ (M.op y X0) = X0 := by
        intro X0 X3
        first
        | (have i₁ := b0e2930 X0 X3
           have i₂ := b0e134 X0 X3 X3
           grind)
        | exact superpose b0e134 b0e2930
        | (have j0 := b0e2930 X0 X3
           grind)
        | exact resolve b0e2930 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e134 b0e2930
      have b0e3072 : ∀ X0 X1 : G, (M.op y (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X1 (σ X0)
           have i₂ := b0e87 X0 X0
           grind)
        | exact superpose b0e87 b0e41
        | (have j1 := b0e87 X0 X0
           grind)
        | exact resolve b0e41 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e3138 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e87 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e3140 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e3138 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3138
      have b0e3147 : ∀ X0 X1 : G, (M.op y (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e3072 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3072
      have b0e4793 : ∀ X0 X1 : G, (k X1 (M.op y X0)) = X1 ∨ (k X1 (M.op y X0)) = X1 := by
        intro X0 X1
        grind
      clear b0e666
      have b0e4926 : ∀ X0 X1 : G, (k X1 (M.op y X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e4793 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4793
      have b0e5054 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op y X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e192 X0 (M.op y X1)
           have i₂ := b0e4926 X1 (σ X0)
           grind)
        | exact superpose b0e4926 b0e192
        | exact resolve b0e192 b0e4926
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e5057 : ∀ X0 X1 : G, (k X0 (τ (M.op y X1))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e5054 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e5054
        | exact resolve b0e5054 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5054
      have b0e5093 : ∀ X0 : G, (M.op y X0) = (k (σ y) X0) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2993 X0 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e2993
        | (have j0 := b0e2993 X0 x
           grind)
        | exact resolve b0e2993 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2993
      have b0e5943 : ∀ X0 : G, (σ (M.op y X0)) ≠ (σ (M.op y X0)) ∨ (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
        intro X0
        first
        | (have i₁ := b0e3140 (M.op y X0)
           have i₂ := b0e641 X0
           grind)
        | exact superpose b0e641 b0e3140
        | (have j0 := b0e3140 (M.op y X0)
           grind)
        | exact resolve b0e3140 b0e641
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e641 b0e3140
      have b0e5952 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
        intro X0
        first
        | (have j0 := b0e5943 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5943
      have b0e16690 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e192 y X0
           have i₂ := b0e5093 X0
           grind)
        | exact superpose b0e5093 b0e192
        | (have j1 := b0e5093 X0
           grind)
        | exact resolve b0e192 b0e5093
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e192 b0e5093
      have b0e21850 : (M.op y x) = (k y y) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b0e2481 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e2481
        | exact resolve b0e2481 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2481
      have b0e26738 : ∀ X0 : G, (M.op y (σ (M.op y X0))) = (k (σ (M.op y X0)) (σ (M.op y X0))) ∨ (σ (M.op y X0)) = (M.op y (σ (M.op y X0))) := by
        intro X0
        first
        | (have i₁ := b0e2016 (σ (M.op y X0)) (σ (M.op y X0))
           have i₂ := b0e5952 X0
           grind)
        | exact superpose b0e5952 b0e2016
        | exact resolve b0e2016 b0e5952
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2016 b0e5952
      have b0e26747 : ∀ X0 : G, (M.op y (σ (M.op y X0))) = (σ (k (M.op y X0) (M.op y X0))) ∨ (σ (M.op y X0)) = (M.op y (σ (M.op y X0))) := by
        intro X0
        first
        | (have i₁ := b0e26738 X0
           have i₂ := b0e17 (M.op y X0) (M.op y X0)
           grind)
        | exact superpose b0e17 b0e26738
        | (have j0 := b0e26738 X0
           grind)
        | exact resolve b0e26738 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26738
      have b0e26799 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ (M.op y X0))) ∨ (σ (M.op y X0)) = (M.op y (σ (M.op y X0))) := by
        intro X0
        first
        | (have i₁ := b0e26747 X0
           have i₂ := b0e4926 X0 (M.op y X0)
           grind)
        | exact superpose b0e4926 b0e26747
        | (have j0 := b0e26747 X0
           grind)
        | exact resolve b0e26747 b0e4926
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4926 b0e26747
      have b0e26800 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ (M.op y X0))) := by
        intro X0
        first
        | (have j0 := b0e26799 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26799
      have b0e28676 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e26800 y
           have i₂ := b0e66 y x
           grind)
        | (have i₁ := b0e26800 y
           have i₂ := b0e66 X0 y
           grind)
        | exact superpose b0e66 b0e26800
        | exact resolve b0e26800 b0e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28702 : ∀ X0 X1 : G, (σ (M.op y X0)) = (M.op X1 (σ (M.op y X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e144 (σ (M.op y X0)) X1
           have i₂ := b0e26800 X0
           grind)
        | exact superpose b0e26800 b0e144
        | exact resolve b0e144 b0e26800
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26800
      have b0e29562 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op X1 (σ (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e144 (σ (M.op X0 y)) X1
           have i₂ := b0e28676 X0
           grind)
        | exact superpose b0e28676 b0e144
        | exact resolve b0e144 b0e28676
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e144 b0e28676
      have b0e53962 : ∀ X0 : G, (τ (M.op X0 y)) = (k y (τ y)) ∨ y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e16690 y
           have i₂ := b0e66 y x
           grind)
        | (have i₁ := b0e16690 y
           have i₂ := b0e66 X0 y
           grind)
        | exact superpose b0e66 b0e16690
        | exact resolve b0e16690 b0e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16690
      have b0e106753 : ∀ X0 : G, (M.op X0 y) = (σ (k y (τ y))) ∨ y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e13 (M.op X0 y)
           have i₂ := b0e53962 X0
           grind)
        | exact superpose b0e53962 b0e13
        | (have j1 := b0e53962 X0
           grind)
        | exact resolve b0e13 b0e53962
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53962
      have b0e106775 : ∀ X0 : G, (M.op X0 y) = (k (σ y) y) ∨ y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e106753 X0
           have i₂ := b0e26 y y
           grind)
        | exact superpose b0e26 b0e106753
        | (have j0 := b0e106753 X0
           grind)
        | exact resolve b0e106753 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e106753
      have b0e118799 : ∀ X0 : G, (M.op y x) = (k (σ y) y) ∨ y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e65 X0
           have i₂ := b0e106775 X0
           grind)
        | exact superpose b0e106775 b0e65
        | (have j1 := b0e106775 X0
           grind)
        | exact resolve b0e65 b0e106775
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e118801 : ∀ X0 X1 : G, (M.op X0 y) = (k (σ y) y) ∨ y = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e66 X0 X1
           have i₂ := b0e106775 X1
           grind)
        | exact superpose b0e106775 b0e66
        | (have j1 := b0e106775 X0
           grind)
        | exact resolve b0e66 b0e106775
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e118982 : ∀ X0 : G, y ≠ (k (σ y) y) ∨ y = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b0e106775 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e106775
      have b0e123022 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (M.op y x) = (k (σ y) y) := by
        intro X0
        first
        | (have i₁ := b0e2229 x X0
           have i₂ := b0e118799 x
           grind)
        | exact superpose b0e118799 b0e2229
        | exact resolve b0e2229 b0e118799
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e123048 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ (M.op y x) = (k (σ y) y) := by
        intro X1
        first
        | (have i₁ := b0e29562 x X1
           have i₂ := b0e118799 x
           grind)
        | exact superpose b0e118799 b0e29562
        | exact resolve b0e29562 b0e118799
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118799
      have b0e123164 : (M.op y x) = (k (σ y) y) := by
        first
        | (have r₁ := b0e123022 x
           have r₂ := b0e123048 x
           grind)
        | exact resolve b0e123022 b0e123048
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e123022 b0e123048
      have b0e124348 : ∀ X0 : G, y ≠ (M.op y x) ∨ y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e118982 X0
           have i₂ := b0e123164
           grind)
        | exact superpose b0e123164 b0e118982
        | (have j0 := b0e118982 X0
           grind)
        | exact resolve b0e118982 b0e123164
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e127631 : ∀ X0 X1 : G, y ≠ (M.op X0 y) ∨ y = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e124348 X1
           have i₂ := b0e65 X0
           grind)
        | exact superpose b0e65 b0e124348
        | (have j0 := b0e124348 X1
           grind)
        | exact resolve b0e124348 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e124348
      have b0e127688 : ∀ X0 X2 : G, y ≠ (M.op y X0) ∨ y = (M.op X2 y) ∨ (M.op X0 y) = (k X0 y) ∨ y = (M.op X0 y) := by
        intro X0 X2
        first
        | (have i₁ := b0e127631 x X2
           have i₂ := b0e126 y x X0
           grind)
        | (have i₁ := b0e127631 y x
           have i₂ := b0e126 X0 x y
           grind)
        | exact superpose b0e126 b0e127631
        | (have j0 := b0e127631 X0 X2
           have j1 := b0e126 y x X0
           grind)
        | (have r₁ := b0e127631 X2 x
           have r₂ := b0e126 y x X2
           grind)
        | exact resolve b0e127631 b0e126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e126
      have b0e127761 : ∀ X0 X2 : G, y ≠ (M.op y X0) ∨ y = (M.op X2 y) ∨ (M.op X0 y) = (k X0 y) := by
        intro X0 X2
        first
        | (have j0 := b0e127688 X0 X2
           have j1 := b0e127631 X0 X2
           grind)
        | (have r₁ := b0e127688 y X2
           have r₂ := b0e127631 X0 y
           grind)
        | (have r₁ := b0e127688 X0 X0
           have r₂ := b0e127631 X0 x
           grind)
        | (have r₁ := b0e127688 X0 X2
           have r₂ := b0e127631 X0 x
           grind)
        | exact resolve b0e127688 b0e127631
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127631 b0e127688
      have b0e128106 : ∀ X1 : G, y = (k (σ y) y) ∨ (M.op y y) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op X1 y) := by
        intro X1
        first
        | (have i₁ := b0e2339 y x
           have i₂ := b0e118801 x X1
           grind)
        | exact superpose b0e118801 b0e2339
        | (have j0 := b0e2339 y y
           have j1 := b0e118801 x y
           grind)
        | exact resolve b0e2339 b0e118801
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2339 b0e118801
      have b0e128404 : ∀ X1 : G, y = (k (σ y) y) ∨ (M.op y y) = (k y y) ∨ y = (M.op X1 y) := by
        intro X1
        first
        | (have j0 := b0e128106 X1
           have j1 := b0e127761 y X1
           grind)
        | (have r₁ := b0e128106 X1
           have r₂ := b0e127761 y x
           grind)
        | (have r₁ := b0e128106 y
           have r₂ := b0e127761 y x
           grind)
        | exact resolve b0e128106 b0e127761
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127761 b0e128106
      have b0e128504 : ∀ X1 : G, (M.op y y) = (k y y) ∨ y = (M.op X1 y) := by
        intro X1
        first
        | (have j0 := b0e128404 X1
           have j1 := b0e118982 X1
           grind)
        | (have r₁ := b0e128404 X1
           have r₂ := b0e118982 x
           grind)
        | exact resolve b0e128404 b0e118982
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128404
      have b0e128529 : ∀ X1 : G, (M.op y x) = (k y y) ∨ y = (M.op X1 y) := by
        intro X1
        first
        | (have i₁ := b0e128504 X1
           have i₂ := b0e65 y
           grind)
        | exact superpose b0e65 b0e128504
        | (have j0 := b0e128504 X1
           grind)
        | exact resolve b0e128504 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65 b0e128504
      have b0e128762 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (M.op y x) = (k y y) := by
        intro X0
        first
        | (have i₁ := b0e2229 x X0
           have i₂ := b0e128529 x
           grind)
        | exact superpose b0e128529 b0e2229
        | exact resolve b0e2229 b0e128529
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2229
      have b0e128788 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ (M.op y x) = (k y y) := by
        intro X1
        first
        | (have i₁ := b0e29562 X1 X1
           have i₂ := b0e128529 X1
           grind)
        | exact superpose b0e128529 b0e29562
        | exact resolve b0e29562 b0e128529
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29562 b0e128529
      have b0e128918 : (M.op y x) = (k y y) := by
        first
        | (have r₁ := b0e128762 x
           have r₂ := b0e128788 x
           grind)
        | exact resolve b0e128762 b0e128788
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128762 b0e128788
      have b0e129173 : ∀ X0 : G, (M.op y (σ y)) = (M.op X0 (σ (M.op y x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e3147 y X0
           have i₂ := b0e128918
           grind)
        | exact superpose b0e128918 b0e3147
        | (have j0 := b0e3147 y x
           grind)
        | exact resolve b0e3147 b0e128918
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3147 b0e128918
      have b0e129226 : (M.op y (σ y)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e129173 x
           have i₂ := b0e28702 x x
           grind)
        | exact superpose b0e28702 b0e129173
        | exact resolve b0e129173 b0e28702
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28702 b0e129173
      have b0e129230 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have r₁ := b0e129226
           have r₂ := b0e2536 y
           grind)
        | exact resolve b0e129226 b0e2536
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129226
      have b0e129233 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e129230
           have i₂ := b0e45 (σ y)
           grind)
        | exact superpose b0e45 b0e129230
        | exact resolve b0e129230 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e129230
      have b0e129234 : (σ y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e129233
           have i₂ := b0e127 y
           grind)
        | exact superpose b0e127 b0e129233
        | exact resolve b0e129233 b0e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127 b0e129233
      have b0e129656 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e5057 X0 (σ x)
           have i₂ := b0e129234
           grind)
        | exact superpose b0e129234 b0e5057
        | exact resolve b0e5057 b0e129234
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5057 b0e129234
      have b0e129776 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e129656 X0
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e129656
        | exact resolve b0e129656 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129656
      have b0e130336 : (σ y) = (M.op y x) := by
        first
        | (have i₁ := b0e123164
           have i₂ := b0e129776 (σ y)
           grind)
        | exact superpose b0e129776 b0e123164
        | exact resolve b0e123164 b0e129776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e123164
      have b0e130357 : y = (M.op y x) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b0e21850
           have i₂ := b0e129776 y
           grind)
        | exact superpose b0e129776 b0e21850
        | exact resolve b0e21850 b0e129776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21850
      have b0e130366 : y = (M.op y x) := by grind
      clear b0e130357
      have b0e130394 : y = (σ y) := by
        first
        | (have i₁ := b0e130336
           have i₂ := b0e130366
           grind)
        | exact superpose b0e130366 b0e130336
        | exact resolve b0e130336 b0e130366
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130336
      have b0e131110 : ∀ X0 : G, (M.op X0 y) ≠ (σ (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b0e2536 X0
           have i₂ := b0e130394
           grind)
        | exact superpose b0e130394 b0e2536
        | exact resolve b0e2536 b0e130394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2536
      have b0e131160 : ∀ X0 : G, y ≠ (k y y) ∨ y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e118982 X0
           have i₂ := b0e130394
           grind)
        | exact superpose b0e130394 b0e118982
        | (have j0 := b0e118982 X0
           grind)
        | exact resolve b0e118982 b0e130394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118982
      have b0e131241 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b0e131160 X0
           grind)
        | (have r₁ := b0e131160 X0
           have r₂ := b0e129776 y
           grind)
        | exact resolve b0e131160 b0e129776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129776 b0e131160
      have b0e131256 : ∀ X0 : G, (σ y) ≠ (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e131110 X0
           have i₂ := b0e130366
           grind)
        | exact superpose b0e130366 b0e131110
        | exact resolve b0e131110 b0e130366
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130366 b0e131110
      have b0e131275 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e131256 x
           have i₂ := b0e131241 x
           grind)
        | exact superpose b0e131241 b0e131256
        | exact resolve b0e131256 b0e131241
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e131241 b0e131256
      have b0e131279 : False := by grind
      exact b0e131279
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
          intro X0 X1 X2 X3
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18
          | exact resolve b1e18 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) x) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 x X1 X2
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : ∀ X0 : G, (M.op X0 y) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b1e29 X0 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e29
          | exact resolve b1e29 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e63 : ∀ X0 X3 : G, (M.op X0 y) = (M.op X3 y) := by
          intro X0 X3
          first
          | (have i₁ := b1e29 X3 x x
             have i₂ := b1e29 X0 x x
             grind)
          | exact superpose b1e29 b1e29
          | exact resolve b1e29 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e175 : ∀ X0 : G, (σ y) ≠ (σ (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e24
             have i₂ := b1e63 x X0
             grind)
          | (have i₁ := b1e24
             have i₂ := b1e63 X0 x
             grind)
          | exact superpose b1e63 b1e24
          | exact resolve b1e24 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e63
        have b1e198 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e27 X1 X0
             grind)
          | exact superpose b1e27 b1e13
          | exact resolve b1e13 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e319 : (σ y) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e175 x
             have i₂ := b1e62 x
             grind)
          | exact superpose b1e62 b1e175
          | exact resolve b1e175 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e175
        have b1e2122 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e198
        have b1e2139 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e2122 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e2122
          | exact resolve b1e2122 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2122
        have b1e2566 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e84 x x
             grind)
          | exact superpose b1e84 b1e21
          | (have j1 := b1e84 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e84 x y
             grind)
          | exact resolve b1e21 b1e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e2646 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e2566
        have b1e4740 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e2646
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e2646
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e2646 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2646
        have b1e4741 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e4740
        have b1e4742 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e4741
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e4741
          | exact resolve b1e4741 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4741
        have b1e4743 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e4742
        have b1e4751 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e4743
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e4743
          | exact resolve b1e4743 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4743
        have b1e5924 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e2139 x
             have i₂ := b1e4751
             grind)
          | exact superpose b1e4751 b1e2139
          | exact resolve b1e2139 b1e4751
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2139 b1e4751
        have b1e5963 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e5924
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e5924
          | exact resolve b1e5924 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5924
        have b1e6109 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e5963
             grind)
          | exact superpose b1e5963 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e5963
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5963
        have b1e6110 : x = (M.op x x) ∨ x = y := by grind
        clear b1e6109
        have b1e6121 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e6110
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e6110
          | exact resolve b1e6110 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6110
        have b1e6122 : x = y := by grind
        clear b1e6121
        have b1e6795 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e319
             have i₂ := b1e6122
             grind)
          | exact superpose b1e6122 b1e319
          | exact resolve b1e319 b1e6122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e319
        have b1e6823 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e6795
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e6795
          | exact resolve b1e6795 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6795
        have b1e6828 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e6823
             have i₂ := b1e6122
             grind)
          | exact superpose b1e6122 b1e6823
          | exact resolve b1e6823 b1e6122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6122 b1e6823
        have b1e6829 : False := by grind
        exact b1e6829
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
          intro X0 X1 X2 X3
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e31 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e91 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
        have b2e135 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op X2 X3) X0) := by
          intro X0 X2 X3
          first
          | (have i₁ := b2e12 x X0 X2 X3
             have i₂ := b2e31 x X0
             grind)
          | exact superpose b2e31 b2e12
          | exact resolve b2e12 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e137 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 (M.op X0 X0) X2 X3
             have i₂ := b2e31 (M.op X0 X0) X0
             grind)
          | exact superpose b2e31 b2e12
          | exact resolve b2e12 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e144 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e137 X0 X1 x x
             have i₂ := b2e31 (M.op x x) X0
             grind)
          | exact superpose b2e31 b2e137
          | exact resolve b2e137 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e137
        have b2e1163 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e91 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91
        have b2e1164 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1163
             have r₂ := b2e22
             grind)
          | exact resolve b2e1163 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1163
        have b2e1165 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1164
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1164
          | exact resolve b2e1164 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1164
        have b2e1166 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1165
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1165
          | exact resolve b2e1165 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1165
        have b2e1168 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e1166
             grind)
          | exact superpose b2e1166 b2e22
          | exact resolve b2e22 b2e1166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1177 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e135 X0 (σ x) (σ y)
             have i₂ := b2e1166
             grind)
          | exact superpose b2e1166 b2e135
          | exact resolve b2e135 b2e1166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e135
        have b2e2027 : (σ x) = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e1166
             have i₂ := b2e1177 (σ y)
             grind)
          | exact superpose b2e1177 b2e1166
          | exact resolve b2e1166 b2e1177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1166 b2e1177
        have b2e2646 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e144 (σ y) x
             have i₂ := b2e2027
             grind)
          | exact superpose b2e2027 b2e144
          | exact resolve b2e144 b2e2027
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e144 b2e2027
        have b2e2772 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b2e2646
        have b2e2837 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b2e2772
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e2772
          | exact resolve b2e2772 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2772
        have b2e2899 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e2837
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e2837
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e2837 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2837
        have b2e2908 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b2e2899
        have b2e2916 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e2908
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2908
          | exact resolve b2e2908 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2908
        have b2e2923 : x = (M.op x x) := by
          first
          | (have r₁ := b2e2916
             have r₂ := b2e1168
             grind)
          | exact resolve b2e2916 b2e1168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2916
        have b2e3115 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e2923
             grind)
          | exact superpose b2e2923 b2e20
          | exact resolve b2e20 b2e2923
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2923
        have b2e3172 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1168
             have i₂ := b2e3115
             grind)
          | exact superpose b2e3115 b2e1168
          | exact resolve b2e1168 b2e3115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1168 b2e3115
        have b2e3178 : False := by grind
        exact b2e3178
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e1565 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e93 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e93
          | exact resolve b3e93 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e93
        have b3e1676 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e1565
        have b3e2295 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e1676
             grind)
          | exact superpose b3e1676 b3e13
          | exact resolve b3e13 b3e1676
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2313 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e2295
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e2295
          | exact resolve b3e2295 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2295
        have b3e2331 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e2313
             grind)
          | exact superpose b3e2313 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e2313
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2313
        have b3e2332 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e2331
        have b3e2334 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e2332
             have r₂ := b3e20
             grind)
          | exact resolve b3e2332 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2332
        have b3e2534 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e2334
        have b3e2667 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1676
             have i₂ := b3e2534
             grind)
          | exact superpose b3e2534 b3e1676
          | exact resolve b3e1676 b3e2534
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1676 b3e2534
        have b3e2676 : (σ x) = (σ y) := by grind
        clear b3e2667
        have b3e2750 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e2676
             grind)
          | exact superpose b3e2676 b3e13
          | exact resolve b3e13 b3e2676
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2676
        have b3e2774 : x = y := by
          first
          | (have i₁ := b3e2750
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e2750
          | exact resolve b3e2750 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2750
        have b3e2873 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e2774
             grind)
          | exact superpose b3e2774 b3e21
          | exact resolve b3e21 b3e2774
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3096 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e2873
             grind)
          | exact superpose b3e2873 b3e20
          | exact resolve b3e20 b3e2873
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2873
        have b3e3122 : False := by grind
        exact b3e3122
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
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
            intro X0 X1 X2 X3
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
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e38 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op X2 X3) X0) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e13 x X0 X2 X3
               have i₂ := b5e38 x X0
               grind)
            | exact superpose b5e38 b5e13
            | exact resolve b5e13 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 (M.op X0 X0) X2 X3
               have i₂ := b5e38 (M.op X0 X0) X0
               grind)
            | exact superpose b5e38 b5e13
            | exact resolve b5e13 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op y X0)) := by
            intro X0
            grind
          have b5e55 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e50 X0 X1 x x
               have i₂ := b5e38 (M.op x x) X0
               grind)
            | exact superpose b5e38 b5e50
            | exact resolve b5e50 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e50
          have b5e59 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e63 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e59
          have b5e66 : x = (k x y) := by
            first
            | (have r₁ := b5e63
               have r₂ := b5e21
               grind)
            | exact resolve b5e63 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e84 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b5e129 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e28 X1 X0
               grind)
            | exact superpose b5e28 b5e14
            | exact resolve b5e14 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e445 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b5e129
          have b5e458 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e445 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e445
            | exact resolve b5e445 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e445
          have b5e829 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e84 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e830 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e829
               have r₂ := b5e24
               grind)
            | exact resolve b5e829 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e829
          have b5e831 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e830
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e830
            | exact resolve b5e830 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e830
          have b5e832 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e831
               have i₂ := b5e66
               grind)
            | exact superpose b5e66 b5e831
            | exact resolve b5e831 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66 b5e831
          have b5e833 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e832
               grind)
            | exact superpose b5e832 b5e24
            | exact resolve b5e24 b5e832
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e840 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e49 X0 (σ x) (σ y)
               have i₂ := b5e832
               grind)
            | exact superpose b5e832 b5e49
            | exact resolve b5e49 b5e832
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1050 : (σ x) = (M.op y (σ y)) := by
            first
            | (have i₁ := b5e832
               have i₂ := b5e840 (σ y)
               grind)
            | exact superpose b5e840 b5e832
            | exact resolve b5e832 b5e840
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e832 b5e840
          have b5e1189 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e73 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e1191 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e1189 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1189
          have b5e1268 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e55 (σ y) x
               have i₂ := b5e1050
               grind)
            | exact superpose b5e1050 b5e55
            | exact resolve b5e55 b5e1050
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e1392 : x = (k x (τ (σ x))) := by
            first
            | (have i₁ := b5e458 x
               have i₂ := b5e1268 (σ x)
               grind)
            | exact superpose b5e1268 b5e458
            | exact resolve b5e458 b5e1268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e458 b5e1268
          have b5e1402 : x = (k x x) := by
            first
            | (have i₁ := b5e1392
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e1392
            | exact resolve b5e1392 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1392
          have b5e1477 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e1402
               grind)
            | exact superpose b5e1402 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e1402
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1402
          have b5e1478 : x = (M.op x x) := by grind
          clear b5e1477
          have b5e1543 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e49 X0 x x
               have i₂ := b5e1478
               grind)
            | exact superpose b5e1478 b5e49
            | exact resolve b5e49 b5e1478
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1478
          have b5e1912 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e1191 (M.op y y)
               have i₂ := b5e51 y
               grind)
            | exact superpose b5e51 b5e1191
            | (have j0 := b5e1191 (M.op y y)
               grind)
            | exact resolve b5e1191 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e1191
          have b5e1921 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
          clear b5e1912
          have b5e1928 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b5e1921
               have i₂ := b5e1543 y
               grind)
            | exact superpose b5e1543 b5e1921
            | exact resolve b5e1921 b5e1543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1921
          have b5e1934 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e1928
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1928
            | exact resolve b5e1928 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1928
          have b5e2036 : (σ x) = (M.op x (σ y)) := by
            first
            | (have i₁ := b5e1050
               have i₂ := b5e1543 (σ y)
               grind)
            | exact superpose b5e1543 b5e1050
            | exact resolve b5e1050 b5e1543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1050
          have b5e3297 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e49 X0 (σ y) (σ y)
               have i₂ := b5e1934
               grind)
            | exact superpose b5e1934 b5e49
            | exact resolve b5e49 b5e1934
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e3310 : ∀ X0 : G, (M.op x X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e3297 X0
               have i₂ := b5e1543 X0
               grind)
            | exact superpose b5e1543 b5e3297
            | exact resolve b5e3297 b5e1543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1543 b5e3297
          have b5e3793 : (σ y) = (M.op x (σ y)) := by
            first
            | (have i₁ := b5e1934
               have i₂ := b5e3310 (σ y)
               grind)
            | exact superpose b5e3310 b5e1934
            | exact resolve b5e1934 b5e3310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1934 b5e3310
          have b5e3848 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e3793
               have i₂ := b5e2036
               grind)
            | exact superpose b5e2036 b5e3793
            | exact resolve b5e3793 b5e2036
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2036 b5e3793
          have b5e3860 : False := by grind
          exact b5e3860
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
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
        have b6e44 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e69 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (σ y) X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 (M.op X0 X0) X2 X3
             have i₂ := b6e44 (M.op X0 X0) X0
             grind)
          | exact superpose b6e44 b6e12
          | exact resolve b6e12 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e75 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op X1 (M.op (σ y) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e69 X0 X1 x x
             have i₂ := b6e44 (M.op x x) X0
             grind)
          | exact superpose b6e44 b6e69
          | exact resolve b6e69 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44 b6e69
        have b6e86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e88 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
        have b6e105 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e88
             have r₂ := b6e20
             grind)
          | exact resolve b6e88 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e113 : x = (M.op x y) := by
          first
          | (have r₁ := b6e105
             have r₂ := b6e21
             grind)
          | exact resolve b6e105 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e105
        have b6e119 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e113
             grind)
          | exact superpose b6e113 b6e21
          | exact resolve b6e21 b6e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e121 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 x y
             have i₂ := b6e113
             grind)
          | exact superpose b6e113 b6e12
          | exact resolve b6e12 b6e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1748 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e86 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e86
          | exact resolve b6e86 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e1866 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1748
        have b6e2388 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e75 (M.op X1 X1) X1
             have i₂ := b6e121 (σ y) X1
             grind)
          | exact superpose b6e121 b6e75
          | exact resolve b6e75 b6e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75 b6e121
        have b6e2567 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e2388 y x
             have i₂ := b6e113
             grind)
          | exact superpose b6e113 b6e2388
          | exact resolve b6e2388 b6e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e113 b6e2388
        have b6e2732 : x = (k x x) := by grind
        clear b6e2567
        have b6e2942 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1866
             have i₂ := b6e2732
             grind)
          | exact superpose b6e2732 b6e1866
          | exact resolve b6e1866 b6e2732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1866 b6e2732
        have b6e2956 : (σ x) = (σ y) := by grind
        clear b6e2942
        have b6e2980 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e2956
             grind)
          | exact superpose b6e2956 b6e13
          | exact resolve b6e13 b6e2956
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2956
        have b6e2994 : x = y := by
          first
          | (have i₁ := b6e2980
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e2980
          | exact resolve b6e2980 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2980
        have b6e3003 : False := by grind
        exact b6e3003
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
            intro X0 X1 X2 X3
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
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b7e29 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X2 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e13 X3 (M.op X2 X2) X4 X5
               have i₂ := b7e13 (M.op X2 X2) X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b7e13 x X2 X4 X5
               have i₂ := b7e13 x X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 X1 x x
               have i₂ := b7e13 X2 X1 x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (M.op (M.op X2 X2) (M.op X2 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op X2 X2) x x
               have i₂ := b7e13 (M.op x x) X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op (σ y) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e29 X0 X1 X2 X3 x x
               have i₂ := b7e32 (M.op x x) X2
               grind)
            | exact superpose b7e32 b7e29
            | exact resolve b7e29 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e45 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e48 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e50 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e48
               have r₂ := b7e23
               grind)
            | exact resolve b7e48 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e51 : (σ x) = (σ (k x y)) := by
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
          have b7e54 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e14
            | exact resolve b7e14 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e55 : x = (k x y) := by
            first
            | (have i₁ := b7e54
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e54
            | exact resolve b7e54 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e75 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e55
               grind)
            | exact superpose b7e55 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e76 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e21
               grind)
            | exact resolve b7e75 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e78 : x = (M.op x y) := by
            first
            | (have r₁ := b7e76
               have r₂ := b7e22
               grind)
            | exact resolve b7e76 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e86 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e28 X1 X0
               grind)
            | exact superpose b7e28 b7e14
            | exact resolve b7e14 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e90 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e78
               grind)
            | exact superpose b7e78 b7e22
            | exact resolve b7e22 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e92 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 x y
               have i₂ := b7e78
               grind)
            | exact superpose b7e78 b7e13
            | exact resolve b7e13 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e132 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e30 X0 X1 X2 x y
               have i₂ := b7e78
               grind)
            | exact superpose b7e78 b7e30
            | exact resolve b7e30 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e189 : ∀ X0 X1 X2 X3 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X0) = (M.op X3 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e35 X0 X0 X2
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e35 X0 X1 X2
               have i₂ := b7e18 X0 (M.op X1 X1)
               grind)
            | exact superpose b7e18 b7e35
            | (have j1 := b7e18 X2 X0
               grind)
            | exact resolve b7e35 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e273 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op X0 (M.op x X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e38 x y X1 X0
               have i₂ := b7e78
               grind)
            | exact superpose b7e78 b7e38
            | exact resolve b7e38 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e348 : ∀ X0 : G, (M.op x X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e32 x X0
               have i₂ := b7e92 x X0
               grind)
            | exact superpose b7e92 b7e32
            | exact resolve b7e32 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e600 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X2 X2) (M.op X2 X2)) ∨ (M.op (M.op X2 X2) (M.op X2 X2)) = (M.op X3 X3) ∨ (k X3 (M.op (M.op X2 X2) (M.op X2 X2))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e17 X3 (M.op (M.op X2 X2) (M.op X2 X2))
               have i₂ := b7e36 X0 X1 X2 X3
               grind)
            | exact superpose b7e36 b7e17
            | (have j0 := b7e17 (M.op X2 X2) (M.op X3 X3)
               grind)
            | exact resolve b7e17 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e614 : ∀ X2 X3 : G, (M.op (M.op X2 X2) (M.op X2 X2)) = (M.op X3 X3) ∨ (k X3 (M.op (M.op X2 X2) (M.op X2 X2))) = X3 := by
            intro X2 X3
            first
            | (have j0 := b7e600 x x X2 X3
               grind)
            | (have r₁ := b7e600 X2 X3 x X3
               have r₂ := b7e13 (M.op x x) x X2 X3
               grind)
            | exact resolve b7e600 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e600
          have b7e668 : ∀ X2 X3 : G, (M.op X3 X3) = (M.op (σ y) X2) ∨ (k X3 (M.op (M.op X2 X2) (M.op X2 X2))) = X3 := by
            intro X2 X3
            first
            | (have i₁ := b7e614 X2 X3
               have i₂ := b7e32 (M.op X2 X2) X2
               grind)
            | exact superpose b7e32 b7e614
            | (have j0 := b7e614 X2 X3
               grind)
            | exact resolve b7e614 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e614
          have b7e707 : ∀ X2 X3 : G, (M.op X3 X3) = (M.op x X2) ∨ (k X3 (M.op (M.op X2 X2) (M.op X2 X2))) = X3 := by
            intro X2 X3
            first
            | (have i₁ := b7e668 X2 X3
               have i₂ := b7e348 X2
               grind)
            | exact superpose b7e348 b7e668
            | (have j0 := b7e668 X2 X3
               grind)
            | exact resolve b7e668 b7e348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e668
          have b7e743 : ∀ X2 X3 : G, (k X3 (M.op (σ y) X2)) = X3 ∨ (M.op X3 X3) = (M.op x X2) := by
            intro X2 X3
            first
            | (have i₁ := b7e707 X2 X3
               have i₂ := b7e32 (M.op X2 X2) X2
               grind)
            | exact superpose b7e32 b7e707
            | (have j0 := b7e707 X2 X3
               grind)
            | exact resolve b7e707 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e707
          have b7e754 : ∀ X2 X3 : G, (k X3 (M.op x X2)) = X3 ∨ (M.op X3 X3) = (M.op x X2) := by
            intro X2 X3
            first
            | (have i₁ := b7e743 X2 X3
               have i₂ := b7e348 X2
               grind)
            | exact superpose b7e348 b7e743
            | (have j0 := b7e743 X2 X3
               grind)
            | exact resolve b7e743 b7e348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e743
          have b7e2492 : ∀ X0 : G, (M.op (σ y) y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e273 X0 y
               have i₂ := b7e78
               grind)
            | exact superpose b7e78 b7e273
            | exact resolve b7e273 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e273
          have b7e2598 : ∀ X0 : G, (M.op x y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e2492 X0
               have i₂ := b7e348 y
               grind)
            | exact superpose b7e348 b7e2492
            | exact resolve b7e2492 b7e348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e348 b7e2492
          have b7e2620 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e2598 X0
               have i₂ := b7e78
               grind)
            | exact superpose b7e78 b7e2598
            | exact resolve b7e2598 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2598
          have b7e2775 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e61 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e2777 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e2775 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2775
          have b7e2954 : x = (k x x) := by grind
          clear b7e2620
          have b7e3909 : ∀ X0 X1 : G, (k X1 (M.op x X0)) = X1 ∨ (k X1 (M.op x X0)) = X1 := by
            intro X0 X1
            grind
          clear b7e754
          have b7e4008 : ∀ X0 X1 : G, (k X1 (M.op x X0)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e3909 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3909
          have b7e4368 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op x X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e86 X0 (M.op x X1)
               have i₂ := b7e4008 X1 (σ X0)
               grind)
            | exact superpose b7e4008 b7e86
            | exact resolve b7e86 b7e4008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4008
          have b7e4371 : ∀ X0 X1 : G, (k X0 (τ (M.op x X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e4368 X0 X1
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e4368
            | exact resolve b7e4368 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4368
          have b7e4880 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e2777 x
               have i₂ := b7e2954
               grind)
            | exact superpose b7e2954 b7e2777
            | (have j0 := b7e2777 x
               grind)
            | exact resolve b7e2777 b7e2954
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2954
          have b7e4884 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b7e4880
          have b7e5043 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e132 (σ x) (σ x) X0
               have i₂ := b7e4884
               grind)
            | exact superpose b7e4884 b7e132
            | exact resolve b7e132 b7e4884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e132 b7e4884
          have b7e5602 : (σ y) = (M.op x (σ y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e5043 (σ y)
               grind)
            | exact superpose b7e5043 b7e24
            | exact resolve b7e24 b7e5043
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5043
          have b7e5966 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e4371 X0 (σ y)
               have i₂ := b7e5602
               grind)
            | exact superpose b7e5602 b7e4371
            | exact resolve b7e4371 b7e5602
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4371 b7e5602
          have b7e5983 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b7e5966 X0
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e5966
            | exact resolve b7e5966 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5966
          have b7e6059 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) := by
            intro X0
            first
            | (have i₁ := b7e86 X0 y
               have i₂ := b7e5983 (σ X0)
               grind)
            | exact superpose b7e5983 b7e86
            | exact resolve b7e86 b7e5983
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e6063 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e6059 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e6059
            | exact resolve b7e6059 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6059
          have b7e6646 : ∀ X0 X1 X2 : G, (M.op X2 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e189 X1 X1 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6794 : (σ (τ y)) ≠ (σ (τ y)) ∨ (σ (τ y)) = (M.op (σ (τ y)) (σ (τ y))) := by
            first
            | (have i₁ := b7e2777 (τ y)
               have i₂ := b7e6063 (τ y)
               grind)
            | exact superpose b7e6063 b7e2777
            | (have j0 := b7e2777 (τ y)
               grind)
            | exact resolve b7e2777 b7e6063
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2777 b7e6063
          have b7e6808 : (σ (τ y)) = (M.op (σ (τ y)) (σ (τ y))) := by grind
          clear b7e6794
          have b7e6816 : y = (M.op y y) := by
            first
            | (have i₁ := b7e6808
               have i₂ := b7e15 y
               grind)
            | exact superpose b7e15 b7e6808
            | exact resolve b7e6808 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6808
          have b7e6909 : ∀ X0 : G, (M.op x y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e92 X0 y
               have i₂ := b7e6816
               grind)
            | exact superpose b7e6816 b7e92
            | exact resolve b7e92 b7e6816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e6924 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (M.op X1 y) = (k X1 y) ∨ y = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b7e189 y X0 X1 y
               have i₂ := b7e6816
               grind)
            | exact superpose b7e6816 b7e189
            | (have j0 := b7e189 y X1 X1 x
               grind)
            | exact resolve b7e189 b7e6816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e189 b7e6816
          have b7e6926 : ∀ X1 : G, (M.op X1 y) = (k X1 y) ∨ y = (M.op X1 y) := by
            intro X1
            first
            | (have j0 := b7e6924 X1 X1
               have j1 := b7e6646 X1 y x
               grind)
            | (have r₁ := b7e6924 x X1
               have r₂ := b7e6646 x y x
               grind)
            | (have r₁ := b7e6924 x x
               have r₂ := b7e6646 x y x
               grind)
            | exact resolve b7e6924 b7e6646
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6646 b7e6924
          have b7e6939 : ∀ X0 : G, x = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e6909 X0
               have i₂ := b7e78
               grind)
            | exact superpose b7e78 b7e6909
            | exact resolve b7e6909 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78 b7e6909
          have b7e6944 : ∀ X1 : G, (M.op X1 y) = X1 ∨ y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b7e6926 X1
               have i₂ := b7e5983 X1
               grind)
            | exact superpose b7e5983 b7e6926
            | (have j0 := b7e6926 X1
               grind)
            | exact resolve b7e6926 b7e5983
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5983 b7e6926
          have b7e6951 : ∀ X1 : G, x = X1 ∨ y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b7e6944 X1
               have i₂ := b7e6939 X1
               grind)
            | exact superpose b7e6939 b7e6944
            | (have j0 := b7e6944 X1
               grind)
            | exact resolve b7e6944 b7e6939
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6944
          have b7e6957 : ∀ X1 : G, x = y ∨ x = X1 := by
            intro X1
            first
            | (have i₁ := b7e6951 X1
               have i₂ := b7e6939 X1
               grind)
            | exact superpose b7e6939 b7e6951
            | (have j0 := b7e6951 y
               grind)
            | exact resolve b7e6951 b7e6939
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6939 b7e6951
          have b7e6961 : ∀ X1 : G, x = X1 := by
            intro X1
            first
            | (have j0 := b7e6957 X1
               grind)
            | (have r₁ := b7e6957 X1
               have r₂ := b7e90
               grind)
            | (have r₁ := b7e6957 y
               have r₂ := b7e90
               grind)
            | exact resolve b7e6957 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6957
          have b7e7401 : x ≠ x := by
            first
            | (have i₁ := b7e90
               have i₂ := b7e6961 y
               grind)
            | exact superpose b7e6961 b7e90
            | (have r₁ := b7e90
               have r₂ := b7e6961 y
               grind)
            | exact resolve b7e90 b7e6961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90 b7e6961
          have b7e7417 : False := by grind
          exact b7e7417
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b8e580 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e64 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e581 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e580
               have r₂ := b8e24
               grind)
            | exact resolve b8e580 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e580
          have b8e582 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e581
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e581
            | exact resolve b8e581 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e581
          have b8e583 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
          have b8e963 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e583
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e583
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e583 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e583
          have b8e964 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e963
          have b8e966 : y = (M.op x y) := by
            first
            | (have r₁ := b8e964
               have r₂ := b8e21
               grind)
            | exact resolve b8e964 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e964
          have b8e968 : False := by grind
          exact b8e968

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_x_pyy_pxy_pyx_Equation4502 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4502 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op x y) := by grind
        have b0e21 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e19
          | exact resolve b0e19 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e24 : (σ y) ≠ (σ y) := by
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
      · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
        · have b1e23 : y ≠ (M.op y y) := by grind
          have b1e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : False := by grind
          exact b1e25
        · have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op x y) := by grind
          have b2e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e25 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e20
            | exact resolve b2e20 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e26 : (σ y) ≠ (σ y) := by
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
          have b2e27 : False := by grind
          exact b2e27
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
            intro X0 X1 X2 X3
            grind
          have b3e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e23 : (σ x) = (M.op (σ x) (σ x)) := by grind
          have b3e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b3e19 (τ X0) X1
               have i₂ := b3e15 X0
               grind)
            | exact superpose b3e15 b3e19
            | exact resolve b3e19 b3e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b3e13 X0 X1 (σ x) (σ x)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e13
            | exact resolve b3e13 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e37 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b3e13 X0 X1 y y
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e40 : ∀ X1 : G, (M.op (σ x) X1) = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b3e35 x X1
               have i₂ := b3e37 x X1
               grind)
            | exact superpose b3e37 b3e35
            | exact resolve b3e35 b3e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e35
          have b3e47 : (σ y) ≠ (M.op y (σ y)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e40 (σ y)
               grind)
            | exact superpose b3e40 b3e22
            | exact resolve b3e22 b3e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e40
          have b3e66 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = X0 ∨ (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b3e17 y X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e17
            | (have j0 := b3e17 y X0
               grind)
            | (have r₁ := b3e17 y x
               have r₂ := b3e24
               grind)
            | exact resolve b3e17 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e67 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have j0 := b3e66 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e66
          have b3e138 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b3e37 X0 y
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e37
            | exact resolve b3e37 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e37
          have b3e175 : ∀ X0 : G, y ≠ y ∨ (M.op y y) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b3e16 X0 y
               have i₂ := b3e138 X0
               grind)
            | exact superpose b3e138 b3e16
            | (have j0 := b3e16 X0 y
               grind)
            | (have r₁ := b3e16 X0 y
               have r₂ := b3e138 X0
               grind)
            | exact resolve b3e16 b3e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e138
          have b3e178 : ∀ X0 : G, (M.op y y) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b3e175 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e175
          have b3e181 : ∀ X0 : G, y = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b3e178 X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e178
            | exact resolve b3e178 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e178
          have b3e209 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b3e26 X0 y
               have i₂ := b3e181 (τ X0)
               grind)
            | exact superpose b3e181 b3e26
            | exact resolve b3e26 b3e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26 b3e181
          have b3e1656 : (σ y) = (M.op y (σ y)) ∨ (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b3e67 (σ y)
               have i₂ := b3e209 y
               grind)
            | exact superpose b3e209 b3e67
            | (have j0 := b3e67 (σ y)
               grind)
            | exact resolve b3e67 b3e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e67 b3e209
          have b3e1657 : (σ y) = (M.op y (σ y)) := by grind
          clear b3e1656
          have b3e1661 : False := by grind
          exact b3e1661
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b4e25 : y ≠ (M.op y y) := by grind
            have b4e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : False := by grind
            exact b4e27
          · have b5e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
              intro X0 X1 X2 X3
              grind
            have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b5e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op x y) := by grind
            have b5e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
            have b5e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e37 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X0 X1 x y
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e52 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b5e17 (σ x) (σ x)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e17
              | (have r₁ := b5e17 (σ x) (σ x)
                 have r₂ := b5e24
                 grind)
              | exact resolve b5e17 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e56 : (σ x) = (k (σ x) (σ x)) := by grind
            clear b5e52
            have b5e57 : (σ x) = (σ (k x x)) := by
              first
              | (have i₁ := b5e56
                 have i₂ := b5e20 x x
                 grind)
              | exact superpose b5e20 b5e56
              | exact resolve b5e56 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e56
            have b5e71 : (k x x) = (τ (σ x)) := by
              first
              | (have i₁ := b5e15 (k x x)
                 have i₂ := b5e57
                 grind)
              | exact superpose b5e57 b5e15
              | exact resolve b5e15 b5e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e57
            have b5e72 : x = (k x x) := by
              first
              | (have i₁ := b5e71
                 have i₂ := b5e15 x
                 grind)
              | exact superpose b5e15 b5e71
              | exact resolve b5e71 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e71
            have b5e96 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b5e19 x x
                 have i₂ := b5e72
                 grind)
              | exact superpose b5e72 b5e19
              | (have j0 := b5e19 x x
                 grind)
              | exact resolve b5e19 b5e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e72
            have b5e97 : x = (M.op x x) := by grind
            clear b5e96
            have b5e132 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X0 X1 x x
                 have i₂ := b5e97
                 grind)
              | exact superpose b5e97 b5e14
              | exact resolve b5e14 b5e97
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e97
            have b5e135 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
              intro X1
              first
              | (have i₁ := b5e132 x X1
                 have i₂ := b5e37 x X1
                 grind)
              | exact superpose b5e37 b5e132
              | exact resolve b5e132 b5e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e37 b5e132
            have b5e1020 : y = (M.op y y) := by
              first
              | (have i₁ := b5e22
                 have i₂ := b5e135 y
                 grind)
              | exact superpose b5e135 b5e22
              | exact resolve b5e22 b5e135
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e135
            have b5e1021 : False := by grind
            exact b5e1021
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
            intro X0 X1 X2 X3
            grind
          have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b6e28 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) y) = (M.op X0 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e13 X0 y X1 X2
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e33 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 X0 X1 y y
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e45 : ∀ X0 X3 : G, (M.op X0 y) = (M.op X3 y) := by
            intro X0 X3
            first
            | (have i₁ := b6e28 X3 x x
               have i₂ := b6e28 X0 x x
               grind)
            | (have i₁ := b6e28 X0 x x
               have i₂ := b6e28 (M.op x x) x x
               grind)
            | exact superpose b6e28 b6e28
            | exact resolve b6e28 b6e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e28
          have b6e70 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = X0 ∨ (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b6e17 y X0
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e17
            | (have j0 := b6e17 y X0
               grind)
            | (have r₁ := b6e17 y x
               have r₂ := b6e24
               grind)
            | exact resolve b6e17 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e72 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have j0 := b6e70 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e70
          have b6e123 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b6e24
               have i₂ := b6e45 y X0
               grind)
            | (have i₁ := b6e24
               have i₂ := b6e45 X0 y
               grind)
            | exact superpose b6e45 b6e24
            | exact resolve b6e24 b6e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e126 : ∀ X0 X1 : G, y ≠ (M.op X0 y) ∨ (M.op y y) = (k X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b6e16 X1 y
               have i₂ := b6e45 X1 X0
               grind)
            | (have i₁ := b6e16 X1 y
               have i₂ := b6e45 X0 X1
               grind)
            | exact superpose b6e45 b6e16
            | (have j0 := b6e16 X0 y
               grind)
            | exact resolve b6e16 b6e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e45
          have b6e131 : ∀ X0 X1 : G, y = (k X1 y) ∨ y ≠ (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b6e126 X0 X1
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e126
            | (have j0 := b6e126 X0 X1
               grind)
            | (have r₁ := b6e126 y X1
               have r₂ := b6e24
               grind)
            | exact resolve b6e126 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e126
          have b6e136 : ∀ X1 : G, y = (k X1 y) := by
            intro X1
            first
            | (have j0 := b6e131 x X1
               grind)
            | (have r₁ := b6e131 x X1
               have r₂ := b6e123 x
               grind)
            | exact resolve b6e131 b6e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e123 b6e131
          have b6e152 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e13 X1 (M.op X0 X0) X2 X3
               have i₂ := b6e33 (M.op X0 X0) X0
               grind)
            | exact superpose b6e33 b6e13
            | exact resolve b6e13 b6e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e159 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e152 X0 X1 x x
               have i₂ := b6e33 (M.op x x) X0
               grind)
            | exact superpose b6e33 b6e152
            | exact resolve b6e152 b6e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e33 b6e152
          have b6e197 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e26 X0 y
               have i₂ := b6e136 (τ X0)
               grind)
            | exact superpose b6e136 b6e26
            | exact resolve b6e26 b6e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26 b6e136
          have b6e598 : (σ y) = (M.op y (σ y)) ∨ (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b6e197 y
               have i₂ := b6e72 (σ y)
               grind)
            | exact superpose b6e72 b6e197
            | (have j1 := b6e72 (σ y)
               grind)
            | exact resolve b6e197 b6e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e72 b6e197
          have b6e602 : (σ y) = (M.op y (σ y)) := by grind
          clear b6e598
          have b6e612 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e159 (σ y) x
               have i₂ := b6e602
               grind)
            | exact superpose b6e602 b6e159
            | exact resolve b6e159 b6e602
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e159 b6e602
          have b6e662 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e612 (σ x)
               grind)
            | exact superpose b6e612 b6e22
            | (have r₁ := b6e22
               have r₂ := b6e612 (σ x)
               grind)
            | exact resolve b6e22 b6e612
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e612
          have b6e685 : False := by grind
          exact b6e685
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b7e25 : y ≠ (M.op y y) := by grind
            have b7e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e27 : False := by grind
            exact b7e27
          · have b8e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
              intro X0 X1 X2 X3
              grind
            have b8e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op x y) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            have b8e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
            have b8e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
            have b8e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X1 (τ X0)
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e20
              | exact resolve b8e20 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e33 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X0 X1 x y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e43 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op X2 X3) X0) := by
              intro X0 X2 X3
              first
              | (have i₁ := b8e14 x X0 X2 X3
                 have i₂ := b8e33 x X0
                 grind)
              | exact superpose b8e33 b8e14
              | exact resolve b8e14 b8e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e44 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X1 (M.op X0 X0) X2 X3
                 have i₂ := b8e33 (M.op X0 X0) X0
                 grind)
              | exact superpose b8e33 b8e14
              | exact resolve b8e14 b8e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e48 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e44 X0 X1 x x
                 have i₂ := b8e33 (M.op x x) X0
                 grind)
              | exact superpose b8e33 b8e44
              | exact resolve b8e44 b8e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e44
            have b8e52 : y ≠ y ∨ (M.op y y) = (k x y) := by
              first
              | (have i₁ := b8e17 x y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e17
              | (have j0 := b8e17 x y
                 grind)
              | (have r₁ := b8e17 x y
                 have r₂ := b8e22
                 grind)
              | exact resolve b8e17 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e56 : (M.op y y) = (k x y) := by grind
            clear b8e52
            have b8e91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X1 X0
                 have i₂ := b8e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b8e19 b8e20
              | (have j1 := b8e19 (σ X1) (σ X1)
                 grind)
              | exact resolve b8e20 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e93 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X2) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e18 X0 X1
                 have i₂ := b8e19 X0 X2
                 grind)
              | exact superpose b8e19 b8e18
              | (have j0 := b8e18 X0 X1
                 have j1 := b8e19 X0 X2
                 grind)
              | (have r₁ := b8e18 X0 X1
                 have r₂ := b8e19 X0 X1
                 grind)
              | (have r₁ := b8e18 X1 X1
                 have r₂ := b8e19 X1 X1
                 grind)
              | exact resolve b8e18 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e103 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b8e24
                 have i₂ := b8e19 (σ x) X0
                 grind)
              | exact superpose b8e19 b8e24
              | (have j1 := b8e19 (σ x) X0
                 grind)
              | (have r₁ := b8e24
                 have r₂ := b8e19 (σ x) x
                 grind)
              | (have r₁ := b8e24
                 have r₂ := b8e19 (σ x) (σ x)
                 grind)
              | exact resolve b8e24 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e104 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
              intro X0
              first
              | (have j0 := b8e103 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e103
            have b8e106 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X2) = X2 := by
              intro X0 X1 X2
              first
              | (have j0 := b8e93 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e93
            have b8e129 : ∀ X0 X1 : G, (M.op y X0) ≠ (M.op y X0) ∨ (M.op (M.op y X0) X1) = X1 ∨ (M.op (M.op y X0) X1) = (k (M.op y X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e18 (M.op y X0) X1
                 have i₂ := b8e48 X0 (M.op y X0)
                 grind)
              | exact superpose b8e48 b8e18
              | (have j0 := b8e18 (M.op y X0) X1
                 grind)
              | (have r₁ := b8e18 (M.op y X0) X1
                 have r₂ := b8e48 X0 (M.op y X0)
                 grind)
              | exact resolve b8e18 b8e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e133 : ∀ X0 X1 : G, (M.op y X0) ≠ (M.op y X0) ∨ (M.op (M.op y X0) (M.op y X0)) = (k X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e17 X1 (M.op y X0)
                 have i₂ := b8e48 X0 X1
                 grind)
              | exact superpose b8e48 b8e17
              | (have j0 := b8e17 X1 (M.op y X0)
                 grind)
              | (have r₁ := b8e17 X1 (M.op y X0)
                 have r₂ := b8e48 X0 X1
                 grind)
              | exact resolve b8e17 b8e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e137 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op y X0)) = (k X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have j0 := b8e133 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e133
            have b8e138 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = X1 ∨ (M.op (M.op y X0) X1) = (k (M.op y X0) X1) := by
              intro X0 X1
              first
              | (have j0 := b8e129 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e129
            have b8e140 : ∀ X0 X1 : G, (M.op y X0) = (k X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e137 X0 X1
                 have i₂ := b8e48 X0 (M.op y X0)
                 grind)
              | exact superpose b8e48 b8e137
              | exact resolve b8e137 b8e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e137
            have b8e143 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op (M.op y X0) X1) = (k (M.op y X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e138 X0 X1
                 have i₂ := b8e43 X1 y X0
                 grind)
              | exact superpose b8e43 b8e138
              | (have j0 := b8e138 X0 X1
                 grind)
              | exact resolve b8e138 b8e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e138
            have b8e146 : ∀ X0 X1 : G, (M.op y X1) = (k (M.op y X0) X1) ∨ (M.op y X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b8e143 X0 X1
                 have i₂ := b8e43 X1 y X0
                 grind)
              | exact superpose b8e43 b8e143
              | (have j0 := b8e143 X0 X1
                 grind)
              | exact resolve b8e143 b8e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e143
            have b8e151 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b8e15 (k (τ X0) X1)
                 have i₂ := b8e28 X0 X1
                 grind)
              | exact superpose b8e28 b8e15
              | exact resolve b8e15 b8e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e28
            have b8e165 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e15 (k X0 (τ X1))
                 have i₂ := b8e29 X1 X0
                 grind)
              | exact superpose b8e29 b8e15
              | exact resolve b8e15 b8e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e29
            have b8e168 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e151 X1 (τ X0)
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e151
              | exact resolve b8e151 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e151
            have b8e260 : ∀ X0 X1 : G, (τ (M.op y X0)) = (k X1 (τ (M.op y X0))) := by
              intro X0 X1
              first
              | (have i₁ := b8e165 X1 (M.op y X0)
                 have i₂ := b8e140 X0 (σ X1)
                 grind)
              | exact superpose b8e140 b8e165
              | exact resolve b8e165 b8e140
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e140 b8e165
            have b8e743 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b8e20 x X0
                 have i₂ := b8e104 (σ X0)
                 grind)
              | exact superpose b8e104 b8e20
              | (have j1 := b8e104 (σ X0)
                 grind)
              | exact resolve b8e20 b8e104
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e104
            have b8e844 : ∀ X0 : G, (τ (M.op y X0)) = (M.op y (τ (M.op y X0))) ∨ (τ (M.op y X0)) = (M.op y (τ (M.op y X0))) := by
              intro X0
              first
              | (have i₁ := b8e260 X0 (M.op y x)
                 have i₂ := b8e146 x (τ (M.op y X0))
                 grind)
              | exact superpose b8e146 b8e260
              | (have j1 := b8e146 X0 (τ (M.op y X0))
                 grind)
              | exact resolve b8e260 b8e146
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e146 b8e260
            have b8e847 : ∀ X0 : G, (τ (M.op y X0)) = (M.op y (τ (M.op y X0))) := by
              intro X0
              first
              | (have j0 := b8e844 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e844
            have b8e919 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b8e106 X0 X1 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e106
            have b8e920 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b8e919 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e919
            have b8e1173 : (σ y) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b8e23
                 have i₂ := b8e91 x y
                 grind)
              | exact superpose b8e91 b8e23
              | (have j1 := b8e91 y y
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e91 y x
                 grind)
              | exact resolve b8e23 b8e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e91
            have b8e2129 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e23
                 have i₂ := b8e743 y
                 grind)
              | exact superpose b8e743 b8e23
              | (have j1 := b8e743 y
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e743 y
                 grind)
              | exact resolve b8e23 b8e743
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e743
            have b8e2142 : (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
            clear b8e2129
            have b8e2148 : (σ (M.op y y)) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b8e2142
                 have i₂ := b8e56
                 grind)
              | exact superpose b8e56 b8e2142
              | exact resolve b8e2142 b8e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e56 b8e2142
            have b8e2824 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b8e920 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e920
            have b8e2827 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b8e2824 X0
                 have j1 := b8e17 X0 X0
                 grind)
              | (have r₁ := b8e2824 x
                 have r₂ := b8e17 x x
                 grind)
              | exact resolve b8e2824 b8e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2824
            have b8e2927 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
              intro X0
              first
              | (have i₁ := b8e20 X0 X0
                 have i₂ := b8e2827 (σ X0)
                 grind)
              | exact superpose b8e2827 b8e20
              | exact resolve b8e20 b8e2827
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e2931 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
              intro X0
              first
              | (have i₁ := b8e168 X0 X0
                 have i₂ := b8e2827 (τ X0)
                 grind)
              | exact superpose b8e2827 b8e168
              | exact resolve b8e168 b8e2827
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e168
            have b8e2935 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b8e2931 X0
                 have i₂ := b8e2827 X0
                 grind)
              | exact superpose b8e2827 b8e2931
              | exact resolve b8e2931 b8e2827
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2931
            have b8e2939 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b8e2927 X0
                 have i₂ := b8e2827 X0
                 grind)
              | exact superpose b8e2827 b8e2927
              | exact resolve b8e2927 b8e2827
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2827 b8e2927
            have b8e3335 : ∀ X0 X1 : G, (M.op y (τ X0)) = (M.op X1 (τ (M.op X0 X0))) := by
              intro X0 X1
              first
              | (have i₁ := b8e33 X1 (τ X0)
                 have i₂ := b8e2935 X0
                 grind)
              | exact superpose b8e2935 b8e33
              | exact resolve b8e33 b8e2935
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e3348 : ∀ X0 X1 : G, (M.op y X1) = (M.op (τ (M.op X0 X0)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e43 X1 (τ X0) (τ X0)
                 have i₂ := b8e2935 X0
                 grind)
              | exact superpose b8e2935 b8e43
              | exact resolve b8e43 b8e2935
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e43
            have b8e3439 : (σ x) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b8e24
                 have i₂ := b8e2939 x
                 grind)
              | exact superpose b8e2939 b8e24
              | exact resolve b8e24 b8e2939
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e4194 : ∀ X0 : G, (M.op y (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b8e2935 (M.op X0 X0)
                 have i₂ := b8e3348 X0 (τ (M.op X0 X0))
                 grind)
              | exact superpose b8e3348 b8e2935
              | exact resolve b8e2935 b8e3348
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2935 b8e3348
            have b8e4200 : ∀ X0 : G, (τ (M.op y X0)) = (M.op y (τ (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b8e4194 X0
                 have i₂ := b8e33 (M.op X0 X0) X0
                 grind)
              | exact superpose b8e33 b8e4194
              | exact resolve b8e4194 b8e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e33 b8e4194
            have b8e4224 : ∀ X0 : G, (τ (M.op y X0)) = (M.op y (τ X0)) := by
              intro X0
              first
              | (have i₁ := b8e4200 X0
                 have i₂ := b8e3335 X0 y
                 grind)
              | exact superpose b8e3335 b8e4200
              | exact resolve b8e4200 b8e3335
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3335 b8e4200
            have b8e4847 : ∀ X0 : G, (M.op y X0) = (σ (M.op y (τ X0))) := by
              intro X0
              first
              | (have i₁ := b8e16 (M.op y X0)
                 have i₂ := b8e4224 X0
                 grind)
              | exact superpose b8e4224 b8e16
              | exact resolve b8e16 b8e4224
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e5184 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ X0)) := by
              intro X0
              first
              | (have i₁ := b8e4847 (σ X0)
                 have i₂ := b8e15 X0
                 grind)
              | exact superpose b8e15 b8e4847
              | exact resolve b8e4847 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4847
            have b8e6752 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b8e1173
                 have i₂ := b8e19 y x
                 grind)
              | exact superpose b8e19 b8e1173
              | (have j1 := b8e19 (σ y) (σ y)
                 grind)
              | exact resolve b8e1173 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1173
            have b8e6766 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
              first
              | (have r₁ := b8e6752
                 have r₂ := b8e26
                 grind)
              | exact resolve b8e6752 b8e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e6752
            have b8e6773 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b8e6766
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e6766
              | exact resolve b8e6766 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e6766
            have b8e6774 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
            clear b8e6773
            have b8e6780 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b8e6774
                 have i₂ := b8e2939 y
                 grind)
              | exact superpose b8e2939 b8e6774
              | exact resolve b8e6774 b8e2939
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2939 b8e6774
            have b8e6786 : (σ y) = (M.op y (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b8e6780
                 have i₂ := b8e5184 y
                 grind)
              | exact superpose b8e5184 b8e6780
              | exact resolve b8e6780 b8e5184
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e6780
            have b8e6792 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op y (σ y)) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b8e6786
                 have i₂ := b8e2148
                 grind)
              | exact superpose b8e2148 b8e6786
              | exact resolve b8e6786 b8e2148
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2148 b8e6786
            have b8e6795 : (σ x) = (M.op y (σ y)) ∨ (σ y) = (M.op y (σ y)) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b8e6792
                 have i₂ := b8e5184 y
                 grind)
              | exact superpose b8e5184 b8e6792
              | exact resolve b8e6792 b8e5184
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e5184 b8e6792
            have b8e41642 : (τ (σ x)) = (M.op y (τ (σ x))) ∨ (σ y) = (M.op y (σ y)) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b8e847 (σ y)
                 have i₂ := b8e6795
                 grind)
              | exact superpose b8e6795 b8e847
              | exact resolve b8e847 b8e6795
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e847 b8e6795
            have b8e41704 : x = (M.op y x) ∨ (σ y) = (M.op y (σ y)) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b8e41642
                 have i₂ := b8e15 x
                 grind)
              | exact superpose b8e15 b8e41642
              | exact resolve b8e41642 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e41642
            have b8e41705 : (σ y) = (M.op y (σ y)) ∨ x = (M.op y x) := by grind
            clear b8e41704
            have b8e41773 : (τ (σ y)) = (M.op y (τ (σ y))) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b8e4224 (σ y)
                 have i₂ := b8e41705
                 grind)
              | exact superpose b8e41705 b8e4224
              | exact resolve b8e4224 b8e41705
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4224 b8e41705
            have b8e41813 : y = (M.op y y) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b8e41773
                 have i₂ := b8e15 y
                 grind)
              | exact superpose b8e15 b8e41773
              | exact resolve b8e41773 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e41773
            have b8e41835 : x = (M.op y x) := by
              first
              | (have r₁ := b8e41813
                 have r₂ := b8e26
                 grind)
              | exact resolve b8e41813 b8e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e41813
            have b8e42388 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b8e48 x x
                 have i₂ := b8e41835
                 grind)
              | exact superpose b8e41835 b8e48
              | exact resolve b8e48 b8e41835
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e48 b8e41835
            have b8e43048 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b8e3439
                 have i₂ := b8e42388 x
                 grind)
              | exact superpose b8e42388 b8e3439
              | exact resolve b8e3439 b8e42388
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3439 b8e42388
            have b8e43177 : False := by grind
            exact b8e43177
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
            intro X0 X1 X2 X3
            grind
          have b9e21 : y ≠ (M.op x y) := by grind
          have b9e22 : x = (M.op x x) := by grind
          have b9e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e40 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X0 X1 x x
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e13
            | exact resolve b9e13 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e41 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X0 X1 y y
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e13
            | exact resolve b9e13 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e44 : ∀ X1 : G, (M.op x X1) = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b9e40 x X1
               have i₂ := b9e41 x X1
               grind)
            | exact superpose b9e41 b9e40
            | exact resolve b9e40 b9e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e40 b9e41
          have b9e50 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e44 y
               grind)
            | exact superpose b9e44 b9e21
            | exact resolve b9e21 b9e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e44
          have b9e55 : False := by grind
          exact b9e55
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b10e25 : y ≠ (M.op y y) := by grind
            have b10e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e27 : False := by grind
            exact b10e27
          · have b11e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
              intro X0 X1 X2 X3
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op x y) := by grind
            have b11e23 : x = (M.op x x) := by grind
            have b11e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b11e20 (τ X0) X1
                 have i₂ := b11e16 X0
                 grind)
              | exact superpose b11e16 b11e20
              | exact resolve b11e20 b11e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e35 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) x) = (M.op X0 x) := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e14 X0 x X1 X2
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e40 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X0 X1 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e14
              | exact resolve b11e14 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e41 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X0 X1 x x
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e44 : ∀ X1 : G, (M.op (σ y) X1) = (M.op x X1) := by
              intro X1
              first
              | (have i₁ := b11e40 x X1
                 have i₂ := b11e41 x X1
                 grind)
              | exact superpose b11e41 b11e40
              | exact resolve b11e40 b11e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e40
            have b11e52 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e56 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
            clear b11e52
            have b11e57 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b11e56
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e56
              | exact resolve b11e56 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e56
            have b11e60 : (M.op x (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b11e57
                 have i₂ := b11e44 (σ y)
                 grind)
              | exact superpose b11e44 b11e57
              | exact resolve b11e57 b11e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e44 b11e57
            have b11e63 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = X0 ∨ (M.op x X0) = (k x X0) := by
              intro X0
              first
              | (have i₁ := b11e18 x X0
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e18
              | (have j0 := b11e18 x X0
                 grind)
              | (have r₁ := b11e18 x x
                 have r₂ := b11e23
                 grind)
              | exact resolve b11e18 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e64 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ (M.op x X0) = X0 := by
              intro X0
              first
              | (have j0 := b11e63 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e63
            have b11e74 : ∀ X0 X3 : G, (M.op X0 x) = (M.op X3 x) := by
              intro X0 X3
              first
              | (have i₁ := b11e35 X3 x x
                 have i₂ := b11e35 X0 x x
                 grind)
              | (have i₁ := b11e35 X0 x x
                 have i₂ := b11e35 (M.op x x) x x
                 grind)
              | exact superpose b11e35 b11e35
              | exact resolve b11e35 b11e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e35
            have b11e142 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ (M.op x x) = (k X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b11e17 X1 x
                 have i₂ := b11e74 X1 X0
                 grind)
              | (have i₁ := b11e17 X1 x
                 have i₂ := b11e74 X0 X1
                 grind)
              | exact superpose b11e74 b11e17
              | (have j0 := b11e17 X0 x
                 grind)
              | exact resolve b11e17 b11e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e147 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b11e23
                 have i₂ := b11e74 x X0
                 grind)
              | (have i₁ := b11e23
                 have i₂ := b11e74 X0 x
                 grind)
              | exact superpose b11e74 b11e23
              | exact resolve b11e23 b11e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e74
            have b11e149 : ∀ X1 : G, (M.op x x) = (k X1 x) := by
              intro X1
              first
              | (have j0 := b11e142 x X1
                 grind)
              | (have r₁ := b11e142 x X1
                 have r₂ := b11e147 x
                 grind)
              | exact resolve b11e142 b11e147
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e142 b11e147
            have b11e156 : ∀ X1 : G, x = (k X1 x) := by
              intro X1
              first
              | (have i₁ := b11e149 X1
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e149
              | exact resolve b11e149 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e149
            have b11e171 : ∀ X0 X2 X3 : G, (M.op x X0) = (M.op (M.op X2 X3) X0) := by
              intro X0 X2 X3
              first
              | (have i₁ := b11e14 x X0 X2 X3
                 have i₂ := b11e41 x X0
                 grind)
              | exact superpose b11e41 b11e14
              | exact resolve b11e14 b11e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e41
            have b11e218 : (k x y) = (τ (M.op x (σ y))) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e60
                 grind)
              | exact superpose b11e60 b11e15
              | exact resolve b11e15 b11e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e60
            have b11e221 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b11e28 X0 x
                 have i₂ := b11e156 (τ X0)
                 grind)
              | exact superpose b11e156 b11e28
              | exact resolve b11e28 b11e156
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e28 b11e156
            have b11e624 : (σ x) = (M.op x (σ x)) ∨ (σ x) = (M.op x (σ x)) := by
              first
              | (have i₁ := b11e221 x
                 have i₂ := b11e64 (σ x)
                 grind)
              | exact superpose b11e64 b11e221
              | (have j1 := b11e64 (σ x)
                 grind)
              | exact resolve b11e221 b11e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e221
            have b11e628 : (σ x) = (M.op x (σ x)) := by grind
            clear b11e624
            have b11e643 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b11e171 X0 x (σ x)
                 have i₂ := b11e628
                 grind)
              | exact superpose b11e628 b11e171
              | exact resolve b11e171 b11e628
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e171 b11e628
            have b11e984 : (σ y) = (M.op x (σ y)) := by
              first
              | (have i₁ := b11e24
                 have i₂ := b11e643 (σ y)
                 grind)
              | exact superpose b11e643 b11e24
              | exact resolve b11e24 b11e643
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e643
            have b11e1051 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b11e218
                 have i₂ := b11e984
                 grind)
              | exact superpose b11e984 b11e218
              | exact resolve b11e218 b11e984
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e218 b11e984
            have b11e1069 : y = (k x y) := by
              first
              | (have i₁ := b11e1051
                 have i₂ := b11e15 y
                 grind)
              | exact superpose b11e15 b11e1051
              | exact resolve b11e1051 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1051
            have b11e1188 : y = (M.op x y) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b11e64 y
                 have i₂ := b11e1069
                 grind)
              | exact superpose b11e1069 b11e64
              | (have j0 := b11e64 y
                 grind)
              | exact resolve b11e64 b11e1069
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e64 b11e1069
            have b11e1190 : y = (M.op x y) := by grind
            clear b11e1188
            have b11e1192 : False := by grind
            exact b11e1192
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
              intro X0 X1 X2 X3
              grind
            have b12e22 : y ≠ (M.op x y) := by grind
            have b12e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e39 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X0 X1 y y
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e280 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b12e39 X0 y
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e39
              | exact resolve b12e39 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e39
            have b12e347 : y ≠ y := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e280 x
                 grind)
              | exact superpose b12e280 b12e22
              | (have r₁ := b12e22
                 have r₂ := b12e280 x
                 grind)
              | exact resolve b12e22 b12e280
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e280
            have b12e348 : False := by grind
            exact b12e348
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b13e27 : y ≠ (M.op y y) := by grind
              have b13e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : False := by grind
              exact b13e29
            · have b14e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
                intro X0 X1 X2 X3
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : x = (M.op x x) := by grind
              have b14e26 : (σ x) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
              have b14e38 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 X1 (σ x) (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e15
                | exact resolve b14e15 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e39 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 X1 x x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e42 : ∀ X1 : G, (M.op (σ x) X1) = (M.op x X1) := by
                intro X1
                first
                | (have i₁ := b14e38 x X1
                   have i₂ := b14e39 x X1
                   grind)
                | exact superpose b14e39 b14e38
                | exact resolve b14e38 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e38
              have b14e46 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e42 (σ y)
                   grind)
                | exact superpose b14e42 b14e22
                | exact resolve b14e22 b14e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e42
              have b14e79 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X2) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e19 X0 X1
                   have i₂ := b14e20 X0 X2
                   grind)
                | exact superpose b14e20 b14e19
                | (have j0 := b14e19 X0 X1
                   have j1 := b14e20 X0 X2
                   grind)
                | (have r₁ := b14e19 X0 X1
                   have r₂ := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e19 X1 X1
                   have r₂ := b14e20 X1 X1
                   grind)
                | exact resolve b14e19 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e87 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X2) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b14e79 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e79
              have b14e181 : ∀ X0 X2 X3 : G, (M.op x X0) = (M.op (M.op X2 X3) X0) := by
                intro X0 X2 X3
                first
                | (have i₁ := b14e15 x X0 X2 X3
                   have i₂ := b14e39 x X0
                   grind)
                | exact superpose b14e39 b14e15
                | exact resolve b14e15 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e231 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b14e16 (k (τ X0) X1)
                   have i₂ := b14e29 X0 X1
                   grind)
                | exact superpose b14e29 b14e16
                | exact resolve b14e16 b14e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e29
              have b14e1556 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e231 X1 (τ X0)
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e231
                | exact resolve b14e231 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e231
              have b14e1887 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e87 X0 X1 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e87
              have b14e1888 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e1887 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1887
              have b14e6518 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have j0 := b14e1888 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1888
              have b14e6522 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b14e6518 X0
                   have j1 := b14e18 X0 X0
                   grind)
                | (have r₁ := b14e6518 x
                   have r₂ := b14e18 x x
                   grind)
                | exact resolve b14e6518 b14e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6518
              have b14e6707 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
                intro X0
                first
                | (have i₁ := b14e1556 X0 X0
                   have i₂ := b14e6522 (τ X0)
                   grind)
                | exact superpose b14e6522 b14e1556
                | exact resolve b14e1556 b14e6522
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1556
              have b14e6712 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
                intro X0
                first
                | (have i₁ := b14e6707 X0
                   have i₂ := b14e6522 X0
                   grind)
                | exact superpose b14e6522 b14e6707
                | exact resolve b14e6707 b14e6522
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6522 b14e6707
              have b14e6977 : ∀ X0 X1 : G, (M.op x (τ X0)) = (M.op X1 (τ (M.op X0 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b14e39 X1 (τ X0)
                   have i₂ := b14e6712 X0
                   grind)
                | exact superpose b14e6712 b14e39
                | exact resolve b14e39 b14e6712
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e7004 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (M.op X0 X0)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e181 X1 (τ X0) (τ X0)
                   have i₂ := b14e6712 X0
                   grind)
                | exact superpose b14e6712 b14e181
                | exact resolve b14e181 b14e6712
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e181
              have b14e7710 : ∀ X0 : G, (M.op x (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b14e6712 (M.op X0 X0)
                   have i₂ := b14e7004 X0 (τ (M.op X0 X0))
                   grind)
                | exact superpose b14e7004 b14e6712
                | exact resolve b14e6712 b14e7004
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6712 b14e7004
              have b14e7780 : ∀ X0 : G, (τ (M.op x X0)) = (M.op x (τ (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b14e7710 X0
                   have i₂ := b14e39 (M.op X0 X0) X0
                   grind)
                | exact superpose b14e39 b14e7710
                | exact resolve b14e7710 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e39 b14e7710
              have b14e7806 : ∀ X0 : G, (M.op x (τ X0)) = (τ (M.op x X0)) := by
                intro X0
                first
                | (have i₁ := b14e7780 X0
                   have i₂ := b14e6977 X0 x
                   grind)
                | exact superpose b14e6977 b14e7780
                | exact resolve b14e7780 b14e6977
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6977 b14e7780
              have b14e7962 : ∀ X0 : G, (M.op x X0) = (σ (M.op x (τ X0))) := by
                intro X0
                first
                | (have i₁ := b14e17 (M.op x X0)
                   have i₂ := b14e7806 X0
                   grind)
                | exact superpose b14e7806 b14e17
                | exact resolve b14e17 b14e7806
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7806
              have b14e8324 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
                intro X0
                first
                | (have i₁ := b14e7962 (σ X0)
                   have i₂ := b14e16 X0
                   grind)
                | exact superpose b14e16 b14e7962
                | exact resolve b14e7962 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7962
              have b14e8750 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
                first
                | (have i₁ := b14e46
                   have i₂ := b14e8324 y
                   grind)
                | exact superpose b14e8324 b14e46
                | (have r₁ := b14e46
                   have r₂ := b14e8324 y
                   grind)
                | exact resolve b14e46 b14e8324
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e46 b14e8324
              have b14e8776 : False := by grind
              exact b14e8776
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
              intro X0 X1 X2 X3
              grind
            have b15e22 : y ≠ (M.op x y) := by grind
            have b15e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e37 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X0 X1 y y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e14
              | exact resolve b15e14 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e235 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b15e37 X0 y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e37
              | exact resolve b15e37 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e37
            have b15e298 : y ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e235 x
                 grind)
              | exact superpose b15e235 b15e22
              | (have r₁ := b15e22
                 have r₂ := b15e235 x
                 grind)
              | exact resolve b15e22 b15e235
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e235
            have b15e299 : False := by grind
            exact b15e299
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b16e27 : y ≠ (M.op y y) := by grind
              have b16e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e29 : False := by grind
              exact b16e29
            · have b17e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
                intro X0 X1 X2 X3
                grind
              have b17e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b17e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e24 : x = (M.op x x) := by grind
              have b17e26 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
              have b17e31 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) x) = (M.op X0 x) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X0 x X1 X2
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X0 X1 x x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e46 : ∀ X0 X3 : G, (M.op X0 x) = (M.op X3 x) := by
                intro X0 X3
                first
                | (have i₁ := b17e31 X3 x x
                   have i₂ := b17e31 X0 x x
                   grind)
                | (have i₁ := b17e31 X0 x x
                   have i₂ := b17e31 (M.op x x) x x
                   grind)
                | exact superpose b17e31 b17e31
                | exact resolve b17e31 b17e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e31
              have b17e68 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = X0 ∨ (M.op x X0) = (k x X0) := by
                intro X0
                first
                | (have i₁ := b17e19 x X0
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e19
                | (have j0 := b17e19 x X0
                   grind)
                | (have r₁ := b17e19 x x
                   have r₂ := b17e24
                   grind)
                | exact resolve b17e19 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e70 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ (M.op x X0) = X0 := by
                intro X0
                first
                | (have j0 := b17e68 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e68
              have b17e95 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ (M.op x x) = (k X1 x) := by
                intro X0 X1
                first
                | (have i₁ := b17e18 X1 x
                   have i₂ := b17e46 X1 X0
                   grind)
                | (have i₁ := b17e18 X1 x
                   have i₂ := b17e46 X0 X1
                   grind)
                | exact superpose b17e46 b17e18
                | (have j0 := b17e18 X0 x
                   grind)
                | exact resolve b17e18 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e100 : ∀ X0 : G, x = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b17e24
                   have i₂ := b17e46 x X0
                   grind)
                | (have i₁ := b17e24
                   have i₂ := b17e46 X0 x
                   grind)
                | exact superpose b17e46 b17e24
                | exact resolve b17e24 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46
              have b17e102 : ∀ X1 : G, (M.op x x) = (k X1 x) := by
                intro X1
                first
                | (have j0 := b17e95 x X1
                   grind)
                | (have r₁ := b17e95 x X1
                   have r₂ := b17e100 x
                   grind)
                | exact resolve b17e95 b17e100
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e95 b17e100
              have b17e109 : ∀ X1 : G, x = (k X1 x) := by
                intro X1
                first
                | (have i₁ := b17e102 X1
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e102
                | exact resolve b17e102 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e102
              have b17e167 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op x X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 X1 (M.op X0 X0) X2 X3
                   have i₂ := b17e35 (M.op X0 X0) X0
                   grind)
                | exact superpose b17e35 b17e15
                | exact resolve b17e15 b17e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e174 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x X0)) := by
                intro X0 X1
                first
                | (have i₁ := b17e167 X0 X1 x x
                   have i₂ := b17e35 (M.op x x) X0
                   grind)
                | exact superpose b17e35 b17e167
                | exact resolve b17e167 b17e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e35 b17e167
              have b17e188 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b17e29 X0 x
                   have i₂ := b17e109 (τ X0)
                   grind)
                | exact superpose b17e109 b17e29
                | exact resolve b17e29 b17e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e29 b17e109
              have b17e595 : (σ x) = (M.op x (σ x)) ∨ (σ x) = (M.op x (σ x)) := by
                first
                | (have i₁ := b17e188 x
                   have i₂ := b17e70 (σ x)
                   grind)
                | exact superpose b17e70 b17e188
                | (have j1 := b17e70 (σ x)
                   grind)
                | exact resolve b17e188 b17e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e70 b17e188
              have b17e601 : (σ x) = (M.op x (σ x)) := by grind
              clear b17e595
              have b17e612 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b17e174 (σ x) x
                   have i₂ := b17e601
                   grind)
                | exact superpose b17e601 b17e174
                | exact resolve b17e174 b17e601
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e174 b17e601
              have b17e677 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e612 (σ x)
                   grind)
                | exact superpose b17e612 b17e26
                | (have r₁ := b17e26
                   have r₂ := b17e612 (σ x)
                   grind)
                | exact resolve b17e26 b17e612
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e612
              have b17e682 : False := by grind
              exact b17e682
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
            intro X0 X1 X2 X3
            grind
          have b18e21 : y ≠ (M.op x y) := by grind
          have b18e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e33 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) y) = (M.op X0 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X0 y X1 X2
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e72 : ∀ X0 X3 : G, (M.op X0 y) = (M.op X3 y) := by
            intro X0 X3
            first
            | (have i₁ := b18e33 X3 x x
               have i₂ := b18e33 X0 x x
               grind)
            | (have i₁ := b18e33 X0 x x
               have i₂ := b18e33 (M.op x x) x x
               grind)
            | exact superpose b18e33 b18e33
            | exact resolve b18e33 b18e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e33
          have b18e148 : ∀ X0 : G, y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b18e21
               have i₂ := b18e72 x X0
               grind)
            | (have i₁ := b18e21
               have i₂ := b18e72 X0 x
               grind)
            | exact superpose b18e72 b18e21
            | exact resolve b18e21 b18e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e149 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b18e24
               have i₂ := b18e72 y X0
               grind)
            | (have i₁ := b18e24
               have i₂ := b18e72 X0 y
               grind)
            | exact superpose b18e72 b18e24
            | exact resolve b18e24 b18e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e72
          have b18e150 : False := by grind
          exact b18e150
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b19e25 : y ≠ (M.op y y) := by grind
            have b19e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e27 : False := by grind
            exact b19e27
          · have b20e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
              intro X0 X1 X2 X3
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b20e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op x y) := by grind
            have b20e23 : x ≠ (M.op x x) := by grind
            have b20e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
            have b20e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b20e20 (τ X0) X1
                 have i₂ := b20e16 X0
                 grind)
              | exact superpose b20e16 b20e20
              | exact resolve b20e20 b20e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b20e20 X1 (τ X0)
                 have i₂ := b20e16 X0
                 grind)
              | exact superpose b20e16 b20e20
              | exact resolve b20e20 b20e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b20e15 (k (τ X0) X1)
                 have i₂ := b20e28 X0 X1
                 grind)
              | exact superpose b20e28 b20e15
              | exact resolve b20e15 b20e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e34 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X2 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
              intro X0 X1 X2 X3 X4 X5
              first
              | (have i₁ := b20e14 X3 (M.op X2 X2) X4 X5
                 have i₂ := b20e14 (M.op X2 X2) X2 X0 X1
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e37 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b20e14 X0 X1 (σ x) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e14
              | exact resolve b20e14 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e14 X0 X1 x x
                 have i₂ := b20e14 X2 X1 x x
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e42 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op (σ y) X2) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e34 X0 X1 X2 X3 x x
                 have i₂ := b20e37 (M.op x x) X2
                 grind)
              | exact superpose b20e37 b20e34
              | exact resolve b20e34 b20e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e34
            have b20e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b20e15 (k X0 (τ X1))
                 have i₂ := b20e29 X1 X0
                 grind)
              | exact superpose b20e29 b20e15
              | exact resolve b20e15 b20e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e51 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b20e17 (σ x) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b20e17 (σ x) (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e54 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
            clear b20e51
            have b20e57 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b20e54
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e54
              | exact resolve b20e54 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e54
            have b20e62 : ∀ X0 X2 X3 : G, (M.op (σ y) X0) = (M.op (M.op X2 X3) X0) := by
              intro X0 X2 X3
              first
              | (have i₁ := b20e14 x X0 X2 X3
                 have i₂ := b20e37 x X0
                 grind)
              | exact superpose b20e37 b20e14
              | exact resolve b20e14 b20e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e63 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (σ y) X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 X1 (M.op X0 X0) X2 X3
                 have i₂ := b20e37 (M.op X0 X0) X0
                 grind)
              | exact superpose b20e37 b20e14
              | exact resolve b20e14 b20e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e69 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op X1 (M.op (σ y) X0)) := by
              intro X0 X1
              first
              | (have i₁ := b20e63 X0 X1 x x
                 have i₂ := b20e37 (M.op x x) X0
                 grind)
              | exact superpose b20e37 b20e63
              | exact resolve b20e63 b20e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e63
            have b20e81 : ∀ X0 : G, (σ (k x y)) = (M.op X0 (σ (k x y))) := by
              intro X0
              first
              | (have i₁ := b20e37 X0 (σ y)
                 have i₂ := b20e57
                 grind)
              | exact superpose b20e57 b20e37
              | exact resolve b20e37 b20e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e83 : (σ y) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b20e17 (σ y) (σ y)
                 have i₂ := b20e57
                 grind)
              | exact superpose b20e57 b20e17
              | exact resolve b20e17 b20e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e84 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ (k x y)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b20e14 X0 X1 (σ y) (σ y)
                 have i₂ := b20e57
                 grind)
              | exact superpose b20e57 b20e14
              | exact resolve b20e14 b20e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e85 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (k x y)) X1) := by
              intro X1
              first
              | (have i₁ := b20e84 x X1
                 have i₂ := b20e37 x X1
                 grind)
              | exact superpose b20e37 b20e84
              | exact resolve b20e84 b20e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e84
            have b20e86 : (σ y) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (k y y)) := by
              first
              | (have i₁ := b20e83
                 have i₂ := b20e20 y y
                 grind)
              | exact superpose b20e20 b20e83
              | exact resolve b20e83 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e83
            have b20e93 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b20e20 X1 X0
                 have i₂ := b20e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b20e19 b20e20
              | (have j1 := b20e19 (σ X1) (σ X1)
                 grind)
              | exact resolve b20e20 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e96 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X2) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e18 X0 X1
                 have i₂ := b20e19 X0 X2
                 grind)
              | exact superpose b20e19 b20e18
              | (have j0 := b20e18 X0 X1
                 have j1 := b20e19 X0 X2
                 grind)
              | (have r₁ := b20e18 X0 X1
                 have r₂ := b20e19 X0 X1
                 grind)
              | (have r₁ := b20e18 X1 X1
                 have r₂ := b20e19 X1 X1
                 grind)
              | exact resolve b20e18 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e102 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 X2) ∨ (k X0 X3) = (M.op X3 X0) ∨ (M.op X0 X3) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 X1 X2 X0 X0
                 have i₂ := b20e19 X0 X3
                 grind)
              | exact superpose b20e19 b20e14
              | (have j1 := b20e19 X0 X3
                 grind)
              | exact resolve b20e14 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e103 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X0 X1)) ∨ (k (M.op X0 X1) X3) = (M.op X3 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X3) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 X0 (M.op X2 X3) X2 X3
                 have i₂ := b20e19 (M.op X2 X3) X1
                 grind)
              | exact superpose b20e19 b20e14
              | (have j1 := b20e19 (M.op X0 X1) X3
                 grind)
              | exact resolve b20e14 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e106 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X2) = X2 := by
              intro X0 X1 X2
              first
              | (have j0 := b20e96 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e96
            have b20e107 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 X1) X3) = (M.op X3 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op (σ y) X3) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e103 X0 X1 X2 X3
                 have i₂ := b20e62 X3 X0 X1
                 grind)
              | exact superpose b20e62 b20e103
              | (have j0 := b20e103 X0 X1 X2 X3
                 grind)
              | exact resolve b20e103 b20e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e103
            have b20e108 : ∀ X0 X2 X3 : G, (M.op (σ y) X2) = (M.op X0 X2) ∨ (k X0 X3) = (M.op X3 X0) ∨ (M.op X0 X3) = X3 := by
              intro X0 X2 X3
              first
              | (have i₁ := b20e102 X0 x X2 X3
                 have i₂ := b20e37 x X2
                 grind)
              | exact superpose b20e37 b20e102
              | (have j0 := b20e102 X0 x X2 X3
                 grind)
              | exact resolve b20e102 b20e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e37 b20e102
            have b20e120 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b20e33 X1 (τ X0)
                 have i₂ := b20e16 X0
                 grind)
              | exact superpose b20e16 b20e33
              | exact resolve b20e33 b20e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e33
            have b20e223 : ∀ X0 X1 X2 X3 : G, (k X0 X3) = (M.op X3 X0) ∨ (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X0 X3) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e40 X0 X0 X2
                 have i₂ := b20e19 X0 X1
                 grind)
              | exact superpose b20e19 b20e40
              | (have j1 := b20e19 X0 X3
                 grind)
              | exact resolve b20e40 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e40
            have b20e386 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) X0) ≠ (M.op (M.op X2 X3) X0) ∨ (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X2 X3) X0)) = (k X1 (M.op (M.op X2 X3) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e17 X1 (M.op (M.op X2 X3) X0)
                 have i₂ := b20e42 X2 X3 X0 X1
                 grind)
              | exact superpose b20e42 b20e17
              | (have j0 := b20e17 X1 (M.op (M.op X2 X3) X0)
                 grind)
              | exact resolve b20e17 b20e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e42
            have b20e393 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X2 X3) X0)) = (k X1 (M.op (M.op X2 X3) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have j0 := b20e386 X0 X1 X2 X3
                 grind)
              | (have r₁ := b20e386 X0 X1 X2 X3
                 have r₂ := b20e62 X0 X2 X3
                 grind)
              | exact resolve b20e386 b20e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e386
            have b20e406 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (k X1 (M.op (σ y) X0)) := by
              intro X0 X1
              first
              | (have i₁ := b20e393 X0 X1 x x
                 have i₂ := b20e62 X0 x x
                 grind)
              | exact superpose b20e62 b20e393
              | exact resolve b20e393 b20e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e393
            have b20e410 : ∀ X0 X1 : G, (M.op (σ y) X0) = (k X1 (M.op (σ y) X0)) := by
              intro X0 X1
              first
              | (have i₁ := b20e406 X0 X1
                 have i₂ := b20e69 X0 (M.op (σ y) X0)
                 grind)
              | exact superpose b20e69 b20e406
              | exact resolve b20e406 b20e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e69 b20e406
            have b20e700 : ∀ X0 : G, (σ (k x y)) ≠ (σ (k x y)) ∨ (M.op (σ (k x y)) (σ (k x y))) = (k X0 (σ (k x y))) := by
              intro X0
              first
              | (have i₁ := b20e17 X0 (σ (k x y))
                 have i₂ := b20e81 X0
                 grind)
              | exact superpose b20e81 b20e17
              | (have j0 := b20e17 X0 (σ (k x y))
                 grind)
              | (have r₁ := b20e17 X0 (σ (k x y))
                 have r₂ := b20e81 X0
                 grind)
              | exact resolve b20e17 b20e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e715 : ∀ X0 : G, (M.op (σ (k x y)) (σ (k x y))) = (k X0 (σ (k x y))) := by
              intro X0
              first
              | (have j0 := b20e700 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e700
            have b20e725 : ∀ X0 : G, (M.op (σ y) (σ (k x y))) = (k X0 (σ (k x y))) := by
              intro X0
              first
              | (have i₁ := b20e715 X0
                 have i₂ := b20e85 (σ (k x y))
                 grind)
              | exact superpose b20e85 b20e715
              | exact resolve b20e715 b20e85
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e85 b20e715
            have b20e737 : ∀ X0 : G, (σ (k x y)) = (k X0 (σ (k x y))) := by
              intro X0
              first
              | (have i₁ := b20e725 X0
                 have i₂ := b20e81 (σ y)
                 grind)
              | exact superpose b20e81 b20e725
              | exact resolve b20e725 b20e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e81 b20e725
            have b20e1030 : ∀ X0 X1 : G, (M.op (σ y) X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b20e108 X0 x X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e108
            have b20e1055 : ∀ X0 : G, (τ (σ (k x y))) = (k X0 (τ (σ (k x y)))) := by
              intro X0
              first
              | (have i₁ := b20e48 X0 (σ (k x y))
                 have i₂ := b20e737 (σ X0)
                 grind)
              | exact superpose b20e737 b20e48
              | exact resolve b20e48 b20e737
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e48 b20e737
            have b20e1057 : ∀ X0 : G, (k x y) = (k X0 (k x y)) := by
              intro X0
              first
              | (have i₁ := b20e1055 X0
                 have i₂ := b20e15 (k x y)
                 grind)
              | exact superpose b20e15 b20e1055
              | exact resolve b20e1055 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1055
            have b20e1104 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b20e106 X0 X1 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e106
            have b20e1105 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b20e1104 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1104
            have b20e1128 : ∀ X0 : G, (M.op y x) = (k X0 (M.op y x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
              intro X0
              first
              | (have i₁ := b20e1057 X0
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e1057
              | (have j1 := b20e19 x x
                 grind)
              | exact resolve b20e1057 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1057
            have b20e1143 : ∀ X0 : G, (M.op y x) = (k X0 (M.op y x)) ∨ y = (M.op x y) := by
              intro X0
              first
              | (have j0 := b20e1128 X0
                 grind)
              | (have r₁ := b20e1128 X0
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e1128 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1128
            have b20e1145 : ∀ X0 : G, (M.op y x) = (k X0 (M.op y x)) := by
              intro X0
              first
              | (have j0 := b20e1143 X0
                 grind)
              | (have r₁ := b20e1143 X0
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e1143 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1143
            have b20e1173 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b20e93 y y
                 have i₂ := b20e57
                 grind)
              | exact superpose b20e57 b20e93
              | exact resolve b20e93 b20e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1178 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b20e24
                 have i₂ := b20e93 x y
                 grind)
              | exact superpose b20e93 b20e24
              | (have j1 := b20e93 y y
                 grind)
              | exact resolve b20e24 b20e93
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1238 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b20e93 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e93
            have b20e1239 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b20e1238 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1238
            have b20e1254 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k y y)) := by grind
            clear b20e1173
            have b20e1282 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b20e1178
                 have i₂ := b20e57
                 grind)
              | exact superpose b20e57 b20e1178
              | exact resolve b20e1178 b20e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e57 b20e1178
            have b20e1284 : (σ (k x y)) = (σ (k y y)) := by
              first
              | (have r₁ := b20e1254
                 have r₂ := b20e86
                 grind)
              | exact resolve b20e1254 b20e86
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e86 b20e1254
            have b20e1299 : (σ (k y y)) = (σ (M.op y x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b20e1284
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e1284
              | (have j1 := b20e19 x x
                 grind)
              | exact resolve b20e1284 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1303 : (k x y) = (τ (σ (k y y))) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e1284
                 grind)
              | exact superpose b20e1284 b20e15
              | exact resolve b20e15 b20e1284
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1319 : (k x y) = (k y y) := by
              first
              | (have i₁ := b20e1303
                 have i₂ := b20e15 (k y y)
                 grind)
              | exact superpose b20e15 b20e1303
              | exact resolve b20e1303 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1303
            have b20e1320 : (σ (k y y)) = (σ (M.op y x)) ∨ y = (M.op x y) := by
              first
              | (have r₁ := b20e1299
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e1299 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1299
            have b20e1325 : (σ (k y y)) = (σ (M.op y x)) := by
              first
              | (have r₁ := b20e1320
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e1320 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1320
            have b20e1364 : ∀ X0 X1 X2 X3 : G, (k X0 X3) = (M.op X3 X0) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op (σ y) X2) = X2 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X3) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e107 X0 X0 X2 X3
                 have i₂ := b20e19 X0 X1
                 grind)
              | exact superpose b20e19 b20e107
              | (have j0 := b20e107 X0 X1 X2 X2
                 have j1 := b20e19 X0 X3
                 grind)
              | exact resolve b20e107 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e107
            have b20e1477 : (k y y) = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b20e19 x y
                 have i₂ := b20e1319
                 grind)
              | exact superpose b20e1319 b20e19
              | (have j0 := b20e19 x x
                 grind)
              | exact resolve b20e19 b20e1319
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1319
            have b20e1478 : (k y y) = (M.op y x) ∨ y = (M.op x y) := by
              first
              | (have r₁ := b20e1477
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e1477 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1477
            have b20e1484 : (k y y) = (M.op y x) := by
              first
              | (have r₁ := b20e1478
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e1478 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1478
            have b20e1539 : (M.op y y) = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b20e19 y y
                 have i₂ := b20e1484
                 grind)
              | exact superpose b20e1484 b20e19
              | (have j0 := b20e19 y y
                 grind)
              | exact resolve b20e19 b20e1484
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1484
            have b20e1540 : (M.op y y) = (M.op y x) ∨ y = (M.op y y) := by grind
            clear b20e1539
            have b20e1542 : (M.op y y) = (M.op y x) := by
              first
              | (have r₁ := b20e1540
                 have r₂ := b20e26
                 grind)
              | exact resolve b20e1540 b20e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1540
            have b20e1887 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0
              first
              | (have i₁ := b20e1239 (τ X0)
                 have i₂ := b20e28 X0 (τ X0)
                 grind)
              | exact superpose b20e28 b20e1239
              | (have j0 := b20e1239 (τ X0)
                 grind)
              | exact resolve b20e1239 b20e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28 b20e1239
            have b20e1896 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0
              first
              | (have i₁ := b20e1887 X0
                 have i₂ := b20e16 X0
                 grind)
              | exact superpose b20e16 b20e1887
              | (have j0 := b20e1887 X0
                 grind)
              | exact resolve b20e1887 b20e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1887
            have b20e1903 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b20e1896 X0
                 have i₂ := b20e16 X0
                 grind)
              | exact superpose b20e16 b20e1896
              | (have j0 := b20e1896 X0
                 grind)
              | exact resolve b20e1896 b20e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1896
            have b20e2346 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
              intro X0
              first
              | (have i₁ := b20e1903 (τ X0)
                 have i₂ := b20e120 X0 X0
                 grind)
              | exact superpose b20e120 b20e1903
              | (have j0 := b20e1903 (τ X0)
                 grind)
              | exact resolve b20e1903 b20e120
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1903
            have b20e2717 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ (k x X1) = (M.op X1 x) ∨ (M.op x X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b20e23
                 have i₂ := b20e223 x x X0 X1
                 grind)
              | (have i₁ := b20e23
                 have i₂ := b20e223 x X0 x X1
                 grind)
              | exact superpose b20e223 b20e23
              | (have j1 := b20e223 x X1 x X1
                 grind)
              | (have r₁ := b20e23
                 have r₂ := b20e223 x X1 x x
                 grind)
              | exact resolve b20e23 b20e223
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e2719 : ∀ X0 X1 : G, y ≠ (M.op X0 y) ∨ (k y X1) = (M.op X1 y) ∨ (M.op y X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b20e26
                 have i₂ := b20e223 y y X0 X1
                 grind)
              | (have i₁ := b20e26
                 have i₂ := b20e223 y X0 y X1
                 grind)
              | exact superpose b20e223 b20e26
              | (have j1 := b20e223 y X1 x X1
                 grind)
              | (have r₁ := b20e26
                 have r₂ := b20e223 y X1 x y
                 grind)
              | exact resolve b20e26 b20e223
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e223
            have b20e2941 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b20e1105 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1105
            have b20e2945 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b20e2941 X0
                 have j1 := b20e17 X0 X0
                 grind)
              | (have r₁ := b20e2941 x
                 have r₂ := b20e17 x x
                 grind)
              | exact resolve b20e2941 b20e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2941
            have b20e3061 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
              intro X0
              first
              | (have i₁ := b20e20 X0 X0
                 have i₂ := b20e2945 (σ X0)
                 grind)
              | exact superpose b20e2945 b20e20
              | exact resolve b20e20 b20e2945
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e3065 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
              intro X0
              first
              | (have i₁ := b20e120 X0 X0
                 have i₂ := b20e2945 (τ X0)
                 grind)
              | exact superpose b20e2945 b20e120
              | exact resolve b20e120 b20e2945
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e120
            have b20e3072 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b20e3065 X0
                 have i₂ := b20e2945 X0
                 grind)
              | exact superpose b20e2945 b20e3065
              | exact resolve b20e3065 b20e2945
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e3065
            have b20e3076 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b20e3061 X0
                 have i₂ := b20e2945 X0
                 grind)
              | exact superpose b20e2945 b20e3061
              | exact resolve b20e3061 b20e2945
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2945 b20e3061
            have b20e3278 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (τ (M.op X0 X0)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b20e62 X1 (τ X0) (τ X0)
                 have i₂ := b20e3072 X0
                 grind)
              | exact superpose b20e3072 b20e62
              | exact resolve b20e62 b20e3072
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e7027 : ∀ X0 X1 X2 : G, (M.op (σ y) X2) = (M.op (τ (M.op (σ y) (M.op X0 X1))) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e3278 (M.op X0 X1) X2
                 have i₂ := b20e62 (M.op X0 X1) X0 X1
                 grind)
              | exact superpose b20e62 b20e3278
              | exact resolve b20e3278 b20e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e62 b20e3278
            have b20e8237 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k x y)) := by
              intro X0
              first
              | (have i₁ := b20e410 (σ x) x
                 have i₂ := b20e1282
                 grind)
              | exact superpose b20e1282 b20e410
              | exact resolve b20e410 b20e1282
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e410 b20e1282
            have b20e8266 : ∀ X0 : G, (σ y) = (σ (k y y)) ∨ (σ x) = (k X0 (σ x)) ∨ (σ y) = (σ (k y x)) := by
              intro X0
              first
              | (have i₁ := b20e8237 X0
                 have i₂ := b20e1284
                 grind)
              | exact superpose b20e1284 b20e8237
              | (have j0 := b20e8237 X0
                 grind)
              | exact resolve b20e8237 b20e1284
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1284 b20e8237
            have b20e8282 : ∀ X0 : G, (σ y) = (σ (M.op y x)) ∨ (σ x) = (k X0 (σ x)) ∨ (σ y) = (σ (k y x)) := by
              intro X0
              first
              | (have i₁ := b20e8266 X0
                 have i₂ := b20e1325
                 grind)
              | exact superpose b20e1325 b20e8266
              | (have j0 := b20e8266 X0
                 grind)
              | exact resolve b20e8266 b20e1325
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1325 b20e8266
            have b20e8298 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) := by
              intro X0
              first
              | (have i₁ := b20e8282 X0
                 have i₂ := b20e1542
                 grind)
              | exact superpose b20e1542 b20e8282
              | (have j0 := b20e8282 X0
                 grind)
              | exact resolve b20e8282 b20e1542
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1542 b20e8282
            have b20e33877 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op (σ y) X1) = X1 ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1 X2
              first
              | (have j0 := b20e1364 X0 X2 X1 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1364
            have b20e33882 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op (σ y) X1) = X1 ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1 X2
              first
              | (have j0 := b20e33877 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e33877
            have b20e33923 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1 X2
              first
              | (have j0 := b20e33882 X0 X1 X2
                 have j1 := b20e1030 X0 X1
                 grind)
              | (have r₁ := b20e33882 X0 X1 X2
                 have r₂ := b20e1030 X0 X1
                 grind)
              | (have r₁ := b20e33882 X1 X1 (σ y)
                 have r₂ := b20e1030 X0 X1
                 grind)
              | (have r₁ := b20e33882 (σ y) X1 X2
                 have r₂ := b20e1030 X0 X1
                 grind)
              | exact resolve b20e33882 b20e1030
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1030 b20e33882
            have b20e69730 : ∀ X2 : G, x ≠ (M.op (σ y) x) ∨ (k x X2) = (M.op X2 x) ∨ (M.op x X2) = X2 := by
              intro X2
              first
              | (have i₁ := b20e2717 (τ (M.op (σ y) (M.op x x))) X2
                 have i₂ := b20e7027 x x x
                 grind)
              | exact superpose b20e7027 b20e2717
              | (have j0 := b20e2717 (σ y) X2
                 grind)
              | exact resolve b20e2717 b20e7027
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2717
            have b20e69735 : ∀ X2 : G, (k x X2) = (M.op X2 x) ∨ (M.op x X2) = X2 := by
              intro X2
              first
              | (have j0 := b20e69730 X2
                 have j1 := b20e33923 x X2 X2
                 grind)
              | (have r₁ := b20e69730 X2
                 have r₂ := b20e33923 x x (σ y)
                 grind)
              | (have r₁ := b20e69730 X2
                 have r₂ := b20e33923 (σ y) x X2
                 grind)
              | exact resolve b20e69730 b20e33923
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e69730
            have b20e70039 : ∀ X2 : G, y ≠ (M.op (σ y) y) ∨ (k y X2) = (M.op X2 y) ∨ (M.op y X2) = X2 := by
              intro X2
              first
              | (have i₁ := b20e2719 (τ (M.op (σ y) (M.op x x))) X2
                 have i₂ := b20e7027 x x y
                 grind)
              | exact superpose b20e7027 b20e2719
              | (have j0 := b20e2719 (σ y) X2
                 grind)
              | exact resolve b20e2719 b20e7027
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2719 b20e7027
            have b20e70043 : ∀ X2 : G, (k y X2) = (M.op X2 y) ∨ (M.op y X2) = X2 := by
              intro X2
              first
              | (have j0 := b20e70039 X2
                 have j1 := b20e33923 y X2 X2
                 grind)
              | (have r₁ := b20e70039 X2
                 have r₂ := b20e33923 y x (σ y)
                 grind)
              | (have r₁ := b20e70039 X2
                 have r₂ := b20e33923 (σ y) y X2
                 grind)
              | exact resolve b20e70039 b20e33923
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e33923 b20e70039
            have b20e90317 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have i₁ := b20e2346 (σ x)
                 have i₂ := b20e8298 (σ x)
                 grind)
              | exact superpose b20e8298 b20e2346
              | (have j0 := b20e2346 (σ x)
                 grind)
              | exact resolve b20e2346 b20e8298
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2346 b20e8298
            have b20e90371 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) := by grind
            clear b20e90317
            have b20e90389 : (τ (σ x)) = (τ (M.op (σ x) (σ x))) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have i₁ := b20e90371
                 have i₂ := b20e3072 (σ x)
                 grind)
              | exact superpose b20e3072 b20e90371
              | exact resolve b20e90371 b20e3072
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e3072 b20e90371
            have b20e90400 : (τ (σ x)) = (τ (σ (M.op x x))) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have i₁ := b20e90389
                 have i₂ := b20e3076 x
                 grind)
              | exact superpose b20e3076 b20e90389
              | exact resolve b20e90389 b20e3076
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e3076 b20e90389
            have b20e90402 : (M.op x x) = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have i₁ := b20e90400
                 have i₂ := b20e15 (M.op x x)
                 grind)
              | exact superpose b20e15 b20e90400
              | exact resolve b20e90400 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e90400
            have b20e90403 : x = (M.op x x) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have i₁ := b20e90402
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e90402
              | exact resolve b20e90402 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e90402
            have b20e90404 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
              first
              | (have r₁ := b20e90403
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e90403 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e90403
            have b20e90419 : (k y x) = (τ (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
              first
              | (have i₁ := b20e15 (k y x)
                 have i₂ := b20e90404
                 grind)
              | exact superpose b20e90404 b20e15
              | exact resolve b20e15 b20e90404
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e90404
            have b20e90469 : (σ y) = (σ (M.op y y)) ∨ y = (k y x) := by
              first
              | (have i₁ := b20e90419
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e90419
              | exact resolve b20e90419 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e90419
            have b20e90766 : (M.op y y) = (τ (σ y)) ∨ y = (k y x) := by
              first
              | (have i₁ := b20e15 (M.op y y)
                 have i₂ := b20e90469
                 grind)
              | exact superpose b20e90469 b20e15
              | exact resolve b20e15 b20e90469
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e90469
            have b20e90841 : y = (M.op y y) ∨ y = (k y x) := by
              first
              | (have i₁ := b20e90766
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e90766
              | exact resolve b20e90766 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e90766
            have b20e90863 : y = (k y x) := by
              first
              | (have r₁ := b20e90841
                 have r₂ := b20e26
                 grind)
              | exact resolve b20e90841 b20e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e90841
            have b20e91106 : y = (M.op x y) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b20e70043 x
                 have i₂ := b20e90863
                 grind)
              | exact superpose b20e90863 b20e70043
              | (have j0 := b20e70043 x
                 grind)
              | exact resolve b20e70043 b20e90863
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e70043 b20e90863
            have b20e91129 : x = (M.op y x) := by
              first
              | (have r₁ := b20e91106
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e91106 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e91106
            have b20e91456 : ∀ X0 : G, x = (k X0 x) := by
              intro X0
              first
              | (have i₁ := b20e1145 X0
                 have i₂ := b20e91129
                 grind)
              | exact superpose b20e91129 b20e1145
              | exact resolve b20e1145 b20e91129
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1145 b20e91129
            have b20e91866 : x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b20e69735 x
                 have i₂ := b20e91456 x
                 grind)
              | exact superpose b20e91456 b20e69735
              | (have j0 := b20e69735 x
                 grind)
              | exact resolve b20e69735 b20e91456
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e69735 b20e91456
            have b20e91875 : x = (M.op x x) := by grind
            clear b20e91866
            have b20e91898 : False := by grind
            exact b20e91898
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e23 : x ≠ (M.op x x) := by grind
            have b21e25 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e52 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b21e17 (σ x) (σ x)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e17
              | (have r₁ := b21e17 (σ x) (σ x)
                 have r₂ := b21e25
                 grind)
              | exact resolve b21e17 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e56 : (σ x) = (k (σ x) (σ x)) := by grind
            clear b21e52
            have b21e57 : (σ x) = (σ (k x x)) := by
              first
              | (have i₁ := b21e56
                 have i₂ := b21e20 x x
                 grind)
              | exact superpose b21e20 b21e56
              | exact resolve b21e56 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e56
            have b21e73 : (k x x) = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 (k x x)
                 have i₂ := b21e57
                 grind)
              | exact superpose b21e57 b21e15
              | exact resolve b21e15 b21e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e57
            have b21e74 : x = (k x x) := by
              first
              | (have i₁ := b21e73
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e73
              | exact resolve b21e73 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e73
            have b21e101 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b21e19 x x
                 have i₂ := b21e74
                 grind)
              | exact superpose b21e74 b21e19
              | (have j0 := b21e19 x x
                 grind)
              | exact resolve b21e19 b21e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e74
            have b21e102 : x = (M.op x x) := by grind
            clear b21e101
            have b21e104 : False := by grind
            exact b21e104
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b22e27 : y ≠ (M.op y y) := by grind
              have b22e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e29 : False := by grind
              exact b22e29
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e24 : x ≠ (M.op x x) := by grind
              have b23e26 : (σ x) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e45 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b23e18 (σ x) (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e18
                | (have r₁ := b23e18 (σ x) (σ x)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e18 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e48 : (σ x) = (k (σ x) (σ x)) := by grind
              clear b23e45
              have b23e51 : (σ x) = (σ (k x x)) := by
                first
                | (have i₁ := b23e48
                   have i₂ := b23e21 x x
                   grind)
                | exact superpose b23e21 b23e48
                | exact resolve b23e48 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e48
              have b23e54 : (k x x) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x x)
                   have i₂ := b23e51
                   grind)
                | exact superpose b23e51 b23e16
                | exact resolve b23e16 b23e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e51
              have b23e55 : x = (k x x) := by
                first
                | (have i₁ := b23e54
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e54
                | exact resolve b23e54 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e54
              have b23e66 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b23e55
                   have i₂ := b23e20 x x
                   grind)
                | exact superpose b23e20 b23e55
                | (have j1 := b23e20 x x
                   grind)
                | exact resolve b23e55 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e55
              have b23e77 : x = (M.op x x) := by grind
              clear b23e66
              have b23e82 : False := by grind
              exact b23e82
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
              intro X0 X1 X2 X3
              grind
            have b24e22 : y ≠ (M.op x y) := by grind
            have b24e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e29 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) y) = (M.op X0 y) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 X0 y X1 X2
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e44 : ∀ X0 X3 : G, (M.op X0 y) = (M.op X3 y) := by
              intro X0 X3
              first
              | (have i₁ := b24e29 X3 x x
                 have i₂ := b24e29 X0 x x
                 grind)
              | (have i₁ := b24e29 X0 x x
                 have i₂ := b24e29 (M.op x x) x x
                 grind)
              | exact superpose b24e29 b24e29
              | exact resolve b24e29 b24e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e29
            have b24e99 : ∀ X0 : G, y ≠ (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b24e22
                 have i₂ := b24e44 x X0
                 grind)
              | (have i₁ := b24e22
                 have i₂ := b24e44 X0 x
                 grind)
              | exact superpose b24e44 b24e22
              | exact resolve b24e22 b24e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e100 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b24e26
                 have i₂ := b24e44 y X0
                 grind)
              | (have i₁ := b24e26
                 have i₂ := b24e44 X0 y
                 grind)
              | exact superpose b24e44 b24e26
              | exact resolve b24e26 b24e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e44
            have b24e101 : False := by grind
            exact b24e101
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b25e27 : y ≠ (M.op y y) := by grind
              have b25e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e29 : False := by grind
              exact b25e29
            · have b26e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
                intro X0 X1 X2 X3
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : y ≠ (M.op x y) := by grind
              have b26e24 : x ≠ (M.op x x) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
              have b26e28 : y ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 (τ X0) X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e21
                | exact resolve b26e21 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
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
              have b26e31 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X2 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b26e15 X3 (M.op X2 X2) X4 X5
                   have i₂ := b26e15 (M.op X2 X2) X2 X0 X1
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e32 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
                intro X0 X1 X2 X4 X5
                first
                | (have i₁ := b26e15 x X2 X4 X5
                   have i₂ := b26e15 x X2 X0 X1
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X0 X1 x x
                   have i₂ := b26e15 X2 X1 x x
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (M.op (M.op X2 X2) (M.op X2 X2))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X3 (M.op X2 X2) x x
                   have i₂ := b26e15 (M.op x x) X2 X0 X1
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e41 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k (τ X0) X1)
                   have i₂ := b26e29 X0 X1
                   grind)
                | exact superpose b26e29 b26e16
                | exact resolve b26e16 b26e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29
              have b26e42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X2 X2) ∨ (M.op (M.op X2 X2) (M.op X2 X2)) = (k X3 (M.op X2 X2)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e18 X3 (M.op X2 X2)
                   have i₂ := b26e15 X3 X2 X0 X1
                   grind)
                | exact superpose b26e15 b26e18
                | (have j0 := b26e18 X3 (M.op X2 X2)
                   grind)
                | (have r₁ := b26e18 X0 (M.op (M.op X2 X3) (M.op X2 X3))
                   have r₂ := b26e15 X0 (M.op X2 X3) X2 X3
                   grind)
                | exact resolve b26e18 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e43 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) ≠ X1 ∨ (M.op X1 X1) = (k (M.op X2 X3) X1) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e18 (M.op X2 X3) X1
                   have i₂ := b26e15 X0 X1 X2 X3
                   grind)
                | exact superpose b26e15 b26e18
                | (have j0 := b26e18 (M.op X2 X3) X1
                   grind)
                | (have r₁ := b26e18 X0 (M.op (M.op X2 X3) (M.op X2 X3))
                   have r₂ := b26e15 X0 (M.op X2 X3) X2 X3
                   grind)
                | exact resolve b26e18 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e49 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k X0 (τ X1))
                   have i₂ := b26e30 X1 X0
                   grind)
                | exact superpose b26e30 b26e16
                | exact resolve b26e16 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e53 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e41 X1 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e41
                | exact resolve b26e41 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e41
              have b26e63 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b26e20 b26e21
                | (have j1 := b26e20 (σ X1) (σ X1)
                   grind)
                | exact resolve b26e21 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X2) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e19 X0 X1
                   have i₂ := b26e20 X0 X2
                   grind)
                | exact superpose b26e20 b26e19
                | (have j0 := b26e19 X0 X1
                   have j1 := b26e20 X0 X2
                   grind)
                | (have r₁ := b26e19 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e19 X1 X1
                   have r₂ := b26e20 X1 X1
                   grind)
                | exact resolve b26e19 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e71 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op X1 (M.op X2 X2)) ∨ (k X0 X3) = (M.op X3 X0) ∨ (M.op X0 X3) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X1 X2 X0 X0
                   have i₂ := b26e20 X0 X3
                   grind)
                | exact superpose b26e20 b26e15
                | (have j1 := b26e20 X0 X3
                   grind)
                | exact resolve b26e15 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e73 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
                intro X0
                first
                | (have i₁ := b26e26
                   have i₂ := b26e20 (σ x) X0
                   grind)
                | exact superpose b26e20 b26e26
                | (have j1 := b26e20 (σ x) X0
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ x) x
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ x) (σ x)
                   grind)
                | exact resolve b26e26 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e74 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
                intro X0
                first
                | (have j0 := b26e73 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e73
              have b26e76 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X2) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e67 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e67
              have b26e79 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e49 (k X0 (τ X1)) X2
                   have i₂ := b26e30 X1 X0
                   grind)
                | exact superpose b26e30 b26e49
                | exact resolve b26e49 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30
              have b26e146 : ∀ X0 X1 X2 X3 : G, (k X0 X3) = (M.op X3 X0) ∨ (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X0 X3) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e36 X0 X0 X2
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e36
                | (have j1 := b26e20 X0 X3
                   grind)
                | exact resolve b26e36 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e233 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X4 (M.op (M.op X3 X3) (M.op X3 X3))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e15 X4 (M.op X3 X3) x x
                   have i₂ := b26e31 X1 X2 X3 X0 x x
                   grind)
                | (have i₁ := b26e15 X0 (M.op (M.op X0 X1) X2) X2 X3
                   have i₂ := b26e31 X0 X1 X2 (M.op X2 X3) X4 x
                   grind)
                | exact superpose b26e31 b26e15
                | exact resolve b26e15 b26e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e235 : ∀ X0 X1 X2 X3 X6 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X6 (M.op X3 X3)) := by
                intro X0 X1 X2 X3 X6
                first
                | (have i₁ := b26e36 (M.op x x) X3 X6
                   have i₂ := b26e31 X1 X2 X3 X0 x x
                   grind)
                | (have i₁ := b26e36 X3 (M.op X0 X1) X2
                   have i₂ := b26e31 X0 X1 (M.op X0 X1) X3 x x
                   grind)
                | exact superpose b26e31 b26e36
                | exact resolve b26e36 b26e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e36
              have b26e236 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X6 X7) X3) := by
                intro X0 X1 X2 X3 X6 X7
                first
                | (have i₁ := b26e15 (M.op x x) X3 X6 X7
                   have i₂ := b26e31 X1 X2 X3 X0 x x
                   grind)
                | (have i₁ := b26e15 X3 (M.op X0 X1) X2 X3
                   have i₂ := b26e31 X0 X1 (M.op X0 X1) X3 x x
                   grind)
                | exact superpose b26e31 b26e15
                | exact resolve b26e15 b26e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e254 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X2) ≠ (M.op (M.op X0 X1) (M.op X2 X2)) ∨ (M.op (M.op (M.op X4 X5) X2) (M.op (M.op X4 X5) X2)) = (k X3 (M.op (M.op X4 X5) X2)) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b26e18 X3 (M.op (M.op X4 X5) X2)
                   have i₂ := b26e31 X4 X5 X2 X3 X0 X1
                   grind)
                | (have i₁ := b26e18 (M.op X4 X5) (M.op X2 X2)
                   have i₂ := b26e31 X0 X1 X2 X3 X4 X5
                   grind)
                | exact superpose b26e31 b26e18
                | (have j0 := b26e18 X3 (M.op (M.op X4 X5) X2)
                   grind)
                | exact resolve b26e18 b26e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e259 : ∀ X2 X3 X4 X5 : G, (M.op (M.op (M.op X4 X5) X2) (M.op (M.op X4 X5) X2)) = (k X3 (M.op (M.op X4 X5) X2)) := by
                intro X2 X3 X4 X5
                first
                | (have j0 := b26e254 x x X2 X3 X4 X5
                   grind)
                | (have r₁ := b26e254 x x x X3 X2 X3
                   have r₂ := b26e15 (M.op x x) x X2 X3
                   grind)
                | exact resolve b26e254 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e254
              have b26e292 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 X5) X3) = (M.op X6 (M.op X0 (M.op (M.op X1 X2) X3))) := by
                intro X0 X1 X2 X3 X4 X5 X6
                first
                | (have i₁ := b26e37 X4 X5 X3 X6
                   have i₂ := b26e31 X1 X2 X3 X0 X3 X3
                   grind)
                | (have i₁ := b26e37 X0 X1 (M.op X0 X1) X3
                   have i₂ := b26e31 X0 X1 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)) X4 X5
                   grind)
                | exact superpose b26e31 b26e37
                | exact resolve b26e37 b26e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e342 : ∀ X0 X1 X2 X5 X6 X7 : G, (M.op (M.op X0 X1) X2) = (M.op X5 (M.op (M.op X6 X7) (M.op X2 X2))) := by
                intro X0 X1 X2 X5 X6 X7
                first
                | (have i₁ := b26e31 X6 X7 (M.op X2 X2) X5 x x
                   have i₂ := b26e37 X0 X1 X2 (M.op x x)
                   grind)
                | exact superpose b26e37 b26e31
                | exact resolve b26e31 b26e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e37
              have b26e461 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e21 x X0
                   have i₂ := b26e74 (σ X0)
                   grind)
                | exact superpose b26e74 b26e21
                | (have j1 := b26e74 (σ X0)
                   grind)
                | exact resolve b26e21 b26e74
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e74
              have b26e607 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X4 X5) X2) ≠ (M.op X3 (M.op (M.op X0 X1) (M.op X2 X2))) ∨ (M.op (M.op X0 X1) (M.op X2 X2)) = (k (M.op X6 X7) (M.op (M.op X4 X5) X2)) := by
                intro X0 X1 X2 X3 X4 X5 X6 X7
                first
                | (have i₁ := b26e43 X0 (M.op X2 X2) X2 X3
                   have i₂ := b26e31 X0 X1 X2 X3 X2 X2
                   grind)
                | (have i₁ := b26e43 X0 (M.op (M.op X0 X1) X2) X2 X3
                   have i₂ := b26e31 X0 X1 X2 (M.op (M.op X0 X1) X2) X4 X5
                   grind)
                | exact superpose b26e31 b26e43
                | exact resolve b26e43 b26e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e31 b26e43
              have b26e630 : ∀ X0 X1 X2 X4 X5 X6 X7 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (k (M.op X6 X7) (M.op (M.op X4 X5) X2)) := by
                intro X0 X1 X2 X4 X5 X6 X7
                first
                | (have j0 := b26e607 X0 X1 X2 x X4 X5 X6 X7
                   grind)
                | (have r₁ := b26e607 X6 X7 X2 X5 X0 X1 X6 X7
                   have r₂ := b26e342 X0 X1 X2 X5 X6 X7
                   grind)
                | exact resolve b26e607 b26e342
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e342 b26e607
              have b26e1206 : ∀ X0 X1 X2 X3 : G, (k X0 X3) = (M.op X3 X0) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X3) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e71 X0 X1 X0 X3
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e71
                | (have j0 := b26e71 X0 X1 X2 X3
                   have j1 := b26e20 X0 X3
                   grind)
                | exact resolve b26e71 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e71
              have b26e1551 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e76 X0 X1 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e76
              have b26e1552 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e1551 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1551
              have b26e1632 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e63 x y
                   grind)
                | exact superpose b26e63 b26e22
                | (have j1 := b26e63 y y
                   grind)
                | exact resolve b26e22 b26e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e63
              have b26e7273 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X5 X6) X7) = (M.op (k (M.op X0 X1) (M.op (M.op X2 X3) X4)) X7) := by
                intro X0 X1 X2 X3 X4 X5 X6 X7
                first
                | (have i₁ := b26e32 X5 X6 X7 (M.op x x) (M.op X4 X4)
                   have i₂ := b26e630 x x X4 X2 X3 X0 X1
                   grind)
                | exact superpose b26e630 b26e32
                | exact resolve b26e32 b26e630
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e630
              have b26e7970 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e25
                   have i₂ := b26e461 y
                   grind)
                | exact superpose b26e461 b26e25
                | (have j1 := b26e461 y
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e461 y
                   grind)
                | exact resolve b26e25 b26e461
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e461
              have b26e8013 : (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
              clear b26e7970
              have b26e8020 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ (k x y)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e15 X0 X1 (σ y) (σ x)
                   have i₂ := b26e8013
                   grind)
                | exact superpose b26e8013 b26e15
                | exact resolve b26e15 b26e8013
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e8025 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ (k x y)) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e32 X0 X1 X2 (σ y) (σ x)
                   have i₂ := b26e8013
                   grind)
                | exact superpose b26e8013 b26e32
                | exact resolve b26e32 b26e8013
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e8043 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (σ (k x y)) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e236 X0 X1 X2 X3 (σ y) (σ x)
                   have i₂ := b26e8013
                   grind)
                | exact superpose b26e8013 b26e236
                | exact resolve b26e236 b26e8013
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e236
              have b26e8519 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ (k x X1) = (M.op X1 x) ∨ (M.op x X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e24
                   have i₂ := b26e146 x x X0 X1
                   grind)
                | (have i₁ := b26e24
                   have i₂ := b26e146 x X0 x X1
                   grind)
                | exact superpose b26e146 b26e24
                | (have j1 := b26e146 x X1 x X1
                   grind)
                | (have r₁ := b26e24
                   have r₂ := b26e146 x X1 x x
                   grind)
                | exact resolve b26e24 b26e146
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e146
              have b26e9290 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ (M.op y x)) X1) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
                intro X0 X1
                first
                | (have i₁ := b26e8020 X0 X1
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e8020
                | (have j1 := b26e20 x x
                   grind)
                | exact resolve b26e8020 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e9539 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ (M.op y x)) X1) ∨ y = (M.op x y) := by
                intro X0 X1
                first
                | (have j0 := b26e9290 X0 X1
                   grind)
                | (have r₁ := b26e9290 X0 X1
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e9290 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e9290
              have b26e9560 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ (M.op y x)) X1) := by
                intro X0 X1
                first
                | (have j0 := b26e9539 X0 X1
                   grind)
                | (have r₁ := b26e9539 X0 X1
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e9539 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e9539
              have b26e10518 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ (M.op y x)) X2) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e8025 X0 X1 X2
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e8025
                | (have j1 := b26e20 x x
                   grind)
                | exact resolve b26e8025 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e10875 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ (M.op y x)) X2) ∨ y = (M.op x y) := by
                intro X0 X1 X2
                first
                | (have j0 := b26e10518 X0 X1 X2
                   grind)
                | (have r₁ := b26e10518 X0 X1 X2
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e10518 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e10518
              have b26e10886 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ (M.op y x)) X2) := by
                intro X0 X1 X2
                first
                | (have j0 := b26e10875 X0 X1 X2
                   grind)
                | (have r₁ := b26e10875 X0 X1 X2
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e10875 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e10875
              have b26e11806 : ∀ X0 : G, (M.op (σ (k x y)) X0) = (M.op (σ (M.op y x)) X0) := by
                intro X0
                first
                | (have i₁ := b26e8020 x X0
                   have i₂ := b26e9560 x X0
                   grind)
                | exact superpose b26e9560 b26e8020
                | exact resolve b26e8020 b26e9560
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e8020
              have b26e11842 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X0 X0)) ≠ (M.op (σ (M.op y x)) X0) ∨ (M.op (M.op (σ (M.op y x)) X0) (M.op (σ (M.op y x)) X0)) = (k X3 (M.op (σ (M.op y x)) X0)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e42 X0 X1 (M.op X1 X1) X3
                   have i₂ := b26e9560 (M.op X1 X1) X1
                   grind)
                | exact superpose b26e9560 b26e42
                | exact resolve b26e42 b26e9560
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e42
              have b26e11954 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 X3) X0)) = (M.op X4 (M.op (σ (M.op y x)) X0)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e233 X1 X2 X3 X0 X4
                   have i₂ := b26e9560 (M.op X0 X0) X0
                   grind)
                | exact superpose b26e9560 b26e233
                | exact resolve b26e233 b26e9560
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e233
              have b26e12012 : ∀ X0 X4 : G, (M.op (σ (k x y)) X0) = (M.op X4 (M.op (σ (M.op y x)) X0)) := by
                intro X0 X4
                first
                | (have i₁ := b26e11954 X0 x x x X4
                   have i₂ := b26e8043 x x x X0
                   grind)
                | exact superpose b26e8043 b26e11954
                | exact resolve b26e11954 b26e8043
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11954
              have b26e12048 : ∀ X0 X3 : G, (M.op (M.op (σ (M.op y x)) X0) (M.op (σ (M.op y x)) X0)) = (k X3 (M.op (σ (M.op y x)) X0)) := by
                intro X0 X3
                first
                | (have j0 := b26e11842 X0 x x X3
                   grind)
                | (have r₁ := b26e11842 x x x X3
                   have r₂ := b26e9560 (M.op x x) x
                   grind)
                | exact resolve b26e11842 b26e9560
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11842
              have b26e12066 : ∀ X0 X4 : G, (M.op (σ (M.op y x)) X0) = (M.op X4 (M.op (σ (M.op y x)) X0)) := by
                intro X0 X4
                first
                | (have i₁ := b26e12012 X0 X4
                   have i₂ := b26e11806 X0
                   grind)
                | exact superpose b26e11806 b26e12012
                | exact resolve b26e12012 b26e11806
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e12012
              have b26e12089 : ∀ X0 X3 : G, (k X3 (M.op (σ (M.op y x)) X0)) = (M.op (σ (k x y)) (M.op (σ (M.op y x)) X0)) := by
                intro X0 X3
                first
                | (have i₁ := b26e12048 X0 X3
                   have i₂ := b26e8025 (σ (M.op y x)) X0 (M.op (σ (M.op y x)) X0)
                   grind)
                | exact superpose b26e8025 b26e12048
                | exact resolve b26e12048 b26e8025
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e12048
              have b26e12108 : ∀ X0 X3 : G, (k X3 (M.op (σ (M.op y x)) X0)) = (M.op (σ (M.op y x)) (M.op (σ (M.op y x)) X0)) := by
                intro X0 X3
                first
                | (have i₁ := b26e12089 X0 X3
                   have i₂ := b26e11806 (M.op (σ (M.op y x)) X0)
                   grind)
                | exact superpose b26e11806 b26e12089
                | exact resolve b26e12089 b26e11806
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e12089
              have b26e12111 : ∀ X0 X3 : G, (M.op (σ (M.op y x)) X0) = (k X3 (M.op (σ (M.op y x)) X0)) := by
                intro X0 X3
                first
                | (have i₁ := b26e12108 X0 X3
                   have i₂ := b26e12066 X0 (σ (M.op y x))
                   grind)
                | exact superpose b26e12066 b26e12108
                | exact resolve b26e12108 b26e12066
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e12066 b26e12108
              have b26e15079 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X3 X3)) = (k X0 (M.op (M.op X1 X2) X3)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e235 (M.op (M.op X1 X2) X3) X1 X2 X3 X4
                   have i₂ := b26e259 X3 X0 X1 X2
                   grind)
                | exact superpose b26e259 b26e235
                | exact resolve b26e235 b26e259
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e235
              have b26e15122 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X6 X7) X5) = (k X0 (M.op (M.op X1 X2) (M.op (M.op X3 X4) X5))) := by
                intro X0 X1 X2 X3 X4 X5 X6 X7
                first
                | (have i₁ := b26e292 (M.op X1 X2) X3 X4 X5 X6 X7 (M.op (M.op X1 X2) (M.op (M.op X3 X4) X5))
                   have i₂ := b26e259 (M.op (M.op X3 X4) X5) X0 X1 X2
                   grind)
                | exact superpose b26e259 b26e292
                | exact resolve b26e292 b26e259
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e292
              have b26e15227 : ∀ X0 X1 X2 X3 : G, (k X3 (τ (M.op (M.op X0 X1) X2))) = (τ (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e49 X3 (M.op (M.op X0 X1) X2)
                   have i₂ := b26e259 X2 (σ X3) X0 X1
                   grind)
                | exact superpose b26e259 b26e49
                | exact resolve b26e49 b26e259
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e49 b26e259
              have b26e15236 : ∀ X0 X1 X2 X3 : G, (k X3 (τ (M.op (M.op X0 X1) X2))) = (τ (M.op (σ (k x y)) (M.op (M.op X0 X1) X2))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15227 X0 X1 X2 X3
                   have i₂ := b26e8025 (M.op X0 X1) X2 (M.op (M.op X0 X1) X2)
                   grind)
                | exact superpose b26e8025 b26e15227
                | exact resolve b26e15227 b26e8025
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e8025 b26e15227
              have b26e15304 : ∀ X0 X5 X6 X7 : G, (M.op (M.op X6 X7) X5) = (k X0 (M.op (σ (k x y)) X5)) := by
                intro X0 X5 X6 X7
                first
                | (have i₁ := b26e15122 X0 x x x x X5 X6 X7
                   have i₂ := b26e8043 (M.op x x) x x X5
                   grind)
                | exact superpose b26e8043 b26e15122
                | exact resolve b26e15122 b26e8043
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e15122
              have b26e15433 : ∀ X0 X1 X2 X3 : G, (k X3 (τ (M.op (M.op X0 X1) X2))) = (τ (M.op (σ (M.op y x)) (M.op (M.op X0 X1) X2))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15236 X0 X1 X2 X3
                   have i₂ := b26e11806 (M.op (M.op X0 X1) X2)
                   grind)
                | exact superpose b26e11806 b26e15236
                | exact resolve b26e15236 b26e11806
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e15236
              have b26e15475 : ∀ X0 X5 X6 X7 : G, (M.op (M.op X6 X7) X5) = (k X0 (M.op (σ (M.op y x)) X5)) := by
                intro X0 X5 X6 X7
                first
                | (have i₁ := b26e15304 X0 X5 X6 X7
                   have i₂ := b26e11806 X5
                   grind)
                | exact superpose b26e11806 b26e15304
                | exact resolve b26e15304 b26e11806
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e15304
              have b26e15566 : ∀ X0 X1 X2 X3 : G, (k X3 (τ (M.op (M.op X0 X1) X2))) = (τ (M.op (σ (k x y)) X2)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15433 X0 X1 X2 X3
                   have i₂ := b26e8043 (σ (M.op y x)) X0 X1 X2
                   grind)
                | exact superpose b26e8043 b26e15433
                | exact resolve b26e15433 b26e8043
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e8043 b26e15433
              have b26e15617 : ∀ X0 X1 X2 X3 : G, (k X3 (τ (M.op (M.op X0 X1) X2))) = (τ (M.op (σ (M.op y x)) X2)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15566 X0 X1 X2 X3
                   have i₂ := b26e11806 X2
                   grind)
                | exact superpose b26e11806 b26e15566
                | exact resolve b26e15566 b26e11806
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11806 b26e15566
              have b26e16176 : ∀ X0 X1 X2 X3 X4 X5 : G, (τ (M.op X0 (M.op X1 X1))) = (k (k X2 (τ X3)) (τ (M.op (M.op X4 X5) X1))) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b26e79 X2 X3 (M.op (M.op X4 X5) X1)
                   have i₂ := b26e15079 (k (σ X2) X3) X4 X5 X1 X0
                   grind)
                | exact superpose b26e15079 b26e79
                | exact resolve b26e79 b26e15079
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e15079
              have b26e16178 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 X1))) = (τ (M.op (σ (M.op y x)) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e16176 X0 X1 x x x x
                   have i₂ := b26e15617 x x X1 (k x (τ x))
                   grind)
                | exact superpose b26e15617 b26e16176
                | exact resolve b26e16176 b26e15617
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e15617 b26e16176
              have b26e19768 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have j0 := b26e1552 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1552
              have b26e19775 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b26e19768 X0
                   have j1 := b26e18 X0 X0
                   grind)
                | (have r₁ := b26e19768 x
                   have r₂ := b26e18 x x
                   grind)
                | exact resolve b26e19768 b26e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e19768
              have b26e20218 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e21 X0 X0
                   have i₂ := b26e19775 (σ X0)
                   grind)
                | exact superpose b26e19775 b26e21
                | exact resolve b26e21 b26e19775
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e20224 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e53 X0 X0
                   have i₂ := b26e19775 (τ X0)
                   grind)
                | exact superpose b26e19775 b26e53
                | exact resolve b26e53 b26e19775
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e53
              have b26e20231 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e20224 X0
                   have i₂ := b26e19775 X0
                   grind)
                | exact superpose b26e19775 b26e20224
                | exact resolve b26e20224 b26e19775
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e20224
              have b26e20237 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e20218 X0
                   have i₂ := b26e19775 X0
                   grind)
                | exact superpose b26e19775 b26e20218
                | exact resolve b26e20218 b26e19775
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e19775 b26e20218
              have b26e20638 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = (M.op (σ (M.op y x)) (τ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e9560 X1 (τ X0)
                   have i₂ := b26e20231 X0
                   grind)
                | exact superpose b26e20231 b26e9560
                | exact resolve b26e9560 b26e20231
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e20641 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (τ (M.op X0 X0)) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X1 X2 (τ X0) (τ X0)
                   have i₂ := b26e20231 X0
                   grind)
                | exact superpose b26e20231 b26e15
                | exact resolve b26e15 b26e20231
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e21788 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e20641 X0 X1 (τ (M.op X0 X0))
                   have i₂ := b26e20231 (M.op X0 X0)
                   grind)
                | exact superpose b26e20231 b26e20641
                | exact resolve b26e20641 b26e20231
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e20641
              have b26e22294 : ∀ X0 : G, (M.op (σ (M.op y x)) (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b26e21788 X0 x
                   have i₂ := b26e20638 (M.op X0 X0) x
                   grind)
                | exact superpose b26e20638 b26e21788
                | exact resolve b26e21788 b26e20638
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e21788
              have b26e22438 : ∀ X0 : G, (M.op (σ (M.op y x)) (τ (M.op X0 X0))) = (τ (M.op (σ (M.op y x)) X0)) := by
                intro X0
                first
                | (have i₁ := b26e22294 X0
                   have i₂ := b26e16178 (M.op X0 X0) X0
                   grind)
                | exact superpose b26e16178 b26e22294
                | exact resolve b26e22294 b26e16178
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e16178 b26e22294
              have b26e22505 : ∀ X0 : G, (M.op (σ (M.op y x)) (τ X0)) = (τ (M.op (σ (M.op y x)) X0)) := by
                intro X0
                first
                | (have i₁ := b26e22438 X0
                   have i₂ := b26e20638 X0 (σ (M.op y x))
                   grind)
                | exact superpose b26e20638 b26e22438
                | exact resolve b26e22438 b26e20638
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e20638 b26e22438
              have b26e62545 : ∀ X0 X1 X2 X3 X4 : G, (τ (M.op (M.op X0 X1) X2)) = (k (k X3 (τ X4)) (τ (M.op (σ (M.op y x)) X2))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e79 X3 X4 (M.op (σ (M.op y x)) X2)
                   have i₂ := b26e15475 (k (σ X3) X4) X2 X0 X1
                   grind)
                | exact superpose b26e15475 b26e79
                | exact resolve b26e79 b26e15475
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e79 b26e15475
              have b26e62546 : ∀ X0 X1 X2 X3 X4 : G, (τ (M.op (M.op X0 X1) X2)) = (k (k X3 (τ X4)) (M.op (σ (M.op y x)) (τ X2))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e62545 X0 X1 X2 X3 X4
                   have i₂ := b26e22505 X2
                   grind)
                | exact superpose b26e22505 b26e62545
                | exact resolve b26e62545 b26e22505
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e22505 b26e62545
              have b26e62984 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X2)) = (M.op (σ (M.op y x)) (τ X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e62546 X0 X1 X2 x x
                   have i₂ := b26e12111 (τ X2) (k x (τ x))
                   grind)
                | exact superpose b26e12111 b26e62546
                | exact resolve b26e62546 b26e12111
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e12111 b26e62546
              have b26e96338 : ∀ X0 X1 X2 X3 : G, (τ (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op (τ X2) (τ X2))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e9560 X3 (τ X2)
                   have i₂ := b26e62984 X0 X1 X2
                   grind)
                | exact superpose b26e62984 b26e9560
                | exact resolve b26e9560 b26e62984
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e9560 b26e62984
              have b26e96531 : ∀ X0 X1 X2 X3 : G, (τ (M.op (M.op X0 X1) X2)) = (M.op X3 (τ (M.op X2 X2))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e96338 X0 X1 X2 X3
                   have i₂ := b26e20231 X2
                   grind)
                | exact superpose b26e20231 b26e96338
                | exact resolve b26e96338 b26e20231
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e20231 b26e96338
              have b26e102535 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = (σ (M.op X0 (τ (M.op X1 X1)))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e17 (M.op (M.op X2 X3) X1)
                   have i₂ := b26e96531 X2 X3 X1 X0
                   grind)
                | exact superpose b26e96531 b26e17
                | exact resolve b26e17 b26e96531
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e96531
              have b26e104041 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b26e1632
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e1632
                | (have j1 := b26e20 (σ y) (σ y)
                   grind)
                | exact resolve b26e1632 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1632
              have b26e104049 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by grind
              clear b26e104041
              have b26e104053 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b26e104049
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e104049 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e104049
              have b26e104057 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b26e104053
                   have i₂ := b26e20237 y
                   grind)
                | exact superpose b26e20237 b26e104053
                | exact resolve b26e104053 b26e20237
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e104053
              have b26e104059 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b26e104057
                   have i₂ := b26e8013
                   grind)
                | exact superpose b26e8013 b26e104057
                | exact resolve b26e104057 b26e8013
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e8013 b26e104057
              have b26e118420 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (σ X0)) = (σ (M.op X3 (τ (σ (M.op X0 X0))))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e102535 X3 (σ X0) X1 X2
                   have i₂ := b26e20237 X0
                   grind)
                | exact superpose b26e20237 b26e102535
                | exact resolve b26e102535 b26e20237
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e20237 b26e102535
              have b26e119321 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (σ X0)) = (σ (M.op X3 (M.op X0 X0))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e118420 X0 X1 X2 X3
                   have i₂ := b26e16 (M.op X0 X0)
                   grind)
                | exact superpose b26e16 b26e118420
                | exact resolve b26e118420 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e118420
              have b26e215274 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e1206 X0 X2 X1 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1206
              have b26e215275 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e215274 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e215274
              have b26e215276 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e215275 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e215275
              have b26e588402 : ∀ X0 X1 X7 : G, x ≠ (M.op (M.op X0 X1) x) ∨ (k x X7) = (M.op X7 x) ∨ (M.op x X7) = X7 := by
                intro X0 X1 X7
                first
                | (have i₁ := b26e8519 (k (M.op x x) (M.op (M.op x x) x)) X7
                   have i₂ := b26e7273 x x x x x X0 X1 x
                   grind)
                | exact superpose b26e7273 b26e8519
                | (have j0 := b26e8519 (M.op X0 X1) X7
                   grind)
                | exact resolve b26e8519 b26e7273
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e7273 b26e8519
              have b26e588404 : ∀ X7 : G, (k x X7) = (M.op X7 x) ∨ (M.op x X7) = X7 := by
                intro X7
                first
                | (have j0 := b26e588402 x x X7
                   have j1 := b26e215276 x X7 x
                   grind)
                | (have r₁ := b26e588402 x x X7
                   have r₂ := b26e215276 x x (M.op x x)
                   grind)
                | (have r₁ := b26e588402 x x X7
                   have r₂ := b26e215276 (M.op x x) x x
                   grind)
                | exact resolve b26e588402 b26e215276
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e215276 b26e588402
              have b26e914326 : (τ (σ x)) = (k x y) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b26e16 (k x y)
                   have i₂ := b26e104059
                   grind)
                | exact superpose b26e104059 b26e16
                | exact resolve b26e16 b26e104059
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e104059
              have b26e914327 : (σ y) = (σ (M.op y y)) ∨ x = (k x y) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b26e914326
                   have i₂ := b26e16 x
                   grind)
                | exact superpose b26e16 b26e914326
                | exact resolve b26e914326 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e914326
              have b26e1375684 : (M.op y y) = (τ (σ y)) ∨ x = (k x y) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b26e16 (M.op y y)
                   have i₂ := b26e914327
                   grind)
                | exact superpose b26e914327 b26e16
                | exact resolve b26e16 b26e914327
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e914327
              have b26e1375685 : y = (M.op y y) ∨ x = (k x y) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b26e1375684
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e1375684
                | exact resolve b26e1375684 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1375684
              have b26e1375686 : x = (k x y) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b26e1375685
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e1375685 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1375685
              have b26e1375703 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b26e588404 y
                   have i₂ := b26e1375686
                   grind)
                | exact superpose b26e1375686 b26e588404
                | (have j0 := b26e588404 y
                   grind)
                | exact resolve b26e588404 b26e1375686
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e588404 b26e1375686
              have b26e1375704 : x = (M.op y x) ∨ y = (M.op x y) := by grind
              clear b26e1375703
              have b26e1375706 : x = (M.op y x) := by
                first
                | (have r₁ := b26e1375704
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e1375704 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1375704
              have b26e1375755 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e15 X0 X1 y x
                   have i₂ := b26e1375706
                   grind)
                | exact superpose b26e1375706 b26e15
                | exact resolve b26e15 b26e1375706
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1375760 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e32 X0 X1 X2 y x
                   have i₂ := b26e1375706
                   grind)
                | exact superpose b26e1375706 b26e32
                | exact resolve b26e32 b26e1375706
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e32
              have b26e1376060 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b26e10886 y x x
                   have i₂ := b26e1375706
                   grind)
                | exact superpose b26e1375706 b26e10886
                | exact resolve b26e10886 b26e1375706
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e10886 b26e1375706
              have b26e1377330 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e1376060 (σ y)
                   grind)
                | exact superpose b26e1376060 b26e22
                | exact resolve b26e22 b26e1376060
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1376060
              have b26e1389288 : ∀ X0 X3 : G, (σ (M.op X3 (M.op X0 X0))) = (M.op x (σ X0)) := by
                intro X0 X3
                first
                | (have i₁ := b26e119321 X0 x x X3
                   have i₂ := b26e1375760 x x (σ X0)
                   grind)
                | exact superpose b26e1375760 b26e119321
                | exact resolve b26e119321 b26e1375760
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e119321 b26e1375760
              have b26e1391274 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
                intro X0
                first
                | (have i₁ := b26e1389288 X0 x
                   have i₂ := b26e1375755 x X0
                   grind)
                | exact superpose b26e1375755 b26e1389288
                | exact resolve b26e1389288 b26e1375755
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1375755 b26e1389288
              have b26e1403716 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
                first
                | (have i₁ := b26e1377330
                   have i₂ := b26e1391274 y
                   grind)
                | exact superpose b26e1391274 b26e1377330
                | (have r₁ := b26e1377330
                   have r₂ := b26e1391274 y
                   grind)
                | exact resolve b26e1377330 b26e1391274
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1377330 b26e1391274
              have b26e1403968 : False := by grind
              exact b26e1403968

/-- `Equation4520`: `x ◇ (y ◇ z) = (x ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_x_pyx_Equation4520 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4520 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4520.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
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
      have b0e65 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e68 : False := by grind
      exact b0e68
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
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b5e42 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e13 X0 x X2 X4
               have i₂ := b5e13 X0 x X2 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 x X0 X1 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b5e44 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e44
            | exact resolve b5e44 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e60 : y = (M.op y y) := by
            first
            | (have i₁ := b5e49
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e49
            | exact resolve b5e49 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e61 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e65 : x = y ∨ x = (k x y) := by grind
          clear b5e61
          have b5e66 : x = (k x y) := by
            first
            | (have r₁ := b5e65
               have r₂ := b5e21
               grind)
            | exact resolve b5e65 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e69 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e140 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (M.op (σ X0) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e42 (σ X0) X1 X2 (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e42
            | exact resolve b5e42 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2028 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e69 y x
               grind)
            | exact superpose b5e69 b5e24
            | (have j1 := b5e69 y x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e69 y x
               grind)
            | exact resolve b5e24 b5e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e2056 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
          clear b5e2028
          have b5e2063 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e2056
               have r₂ := b5e23
               grind)
            | exact resolve b5e2056 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2056
          have b5e2076 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e2063
               have i₂ := b5e66
               grind)
            | exact superpose b5e66 b5e2063
            | exact resolve b5e2063 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66 b5e2063
          have b5e2089 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e42 (σ y) X0 X1 (σ x)
               have i₂ := b5e2076
               grind)
            | exact superpose b5e2076 b5e42
            | exact resolve b5e42 b5e2076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e2076
          have b5e2108 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (σ (M.op y y)) X1) := by
            intro X1
            first
            | (have i₁ := b5e2089 x X1
               have i₂ := b5e140 y x X1
               grind)
            | exact superpose b5e140 b5e2089
            | exact resolve b5e2089 b5e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e140 b5e2089
          have b5e2116 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (σ y) X1) := by
            intro X1
            first
            | (have i₁ := b5e2108 X1
               have i₂ := b5e60
               grind)
            | exact superpose b5e60 b5e2108
            | exact resolve b5e2108 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2108
          have b5e3964 : (σ y) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e2116 (σ y)
               grind)
            | exact superpose b5e2116 b5e24
            | exact resolve b5e24 b5e2116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2116
          have b5e4047 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e3964
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e3964
            | exact resolve b5e3964 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e3964
          have b5e4081 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e4047
               have i₂ := b5e60
               grind)
            | exact superpose b5e60 b5e4047
            | exact resolve b5e4047 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60 b5e4047
          have b5e4082 : False := by grind
          exact b5e4082
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
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ x) (σ y) X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b7e13 X0 x X2 X4
               have i₂ := b7e13 X0 x X2 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e50 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e53 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e50
          have b7e54 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e53
               have r₂ := b7e23
               grind)
            | exact resolve b7e53 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e55 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e54
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e54
            | exact resolve b7e54 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e58 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e55
               grind)
            | exact superpose b7e55 b7e14
            | exact resolve b7e14 b7e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e59 : x = (k x y) := by
            first
            | (have i₁ := b7e58
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e58
            | exact resolve b7e58 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e69 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e59
               grind)
            | exact superpose b7e59 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e70 : x = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e22
               grind)
            | exact resolve b7e69 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e72 : x = (M.op y x) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e21
               grind)
            | exact resolve b7e70 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e102 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e33 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33
            | exact resolve b7e33 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e108 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 (σ y)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X0 X1) X2 X3 (σ y)
               have i₂ := b7e33 X0 X1
               grind)
            | exact superpose b7e33 b7e13
            | exact resolve b7e13 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e110 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e102
               have i₂ := b7e31 y
               grind)
            | exact superpose b7e31 b7e102
            | exact resolve b7e102 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e141 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e36 y X0 X1 x
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e36
            | exact resolve b7e36 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e72
          have b7e178 : (M.op (σ y) (σ y)) = (σ (M.op (M.op y y) (M.op y y))) := by
            first
            | (have i₁ := b7e31 (M.op y y)
               have i₂ := b7e110
               grind)
            | exact superpose b7e110 b7e31
            | exact resolve b7e31 b7e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e185 : (M.op (σ y) (σ y)) = (σ (M.op (M.op y (σ y)) y)) := by
            first
            | (have i₁ := b7e178
               have i₂ := b7e108 y y y y
               grind)
            | exact superpose b7e108 b7e178
            | exact resolve b7e178 b7e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108 b7e178
          have b7e186 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e185
               have i₂ := b7e141 (σ y) y
               grind)
            | exact superpose b7e141 b7e185
            | exact resolve b7e185 b7e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141 b7e185
          have b7e187 : (σ (M.op x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e186
               have i₂ := b7e31 y
               grind)
            | exact superpose b7e31 b7e186
            | exact resolve b7e186 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e186
          have b7e188 : (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b7e187
               have i₂ := b7e110
               grind)
            | exact superpose b7e110 b7e187
            | exact resolve b7e187 b7e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110 b7e187
          have b7e189 : False := by grind
          exact b7e189
        · have b8e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e32 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X5) (M.op X4 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e13 X3 X0 (M.op X4 X2) X5
               have i₂ := b8e13 X0 X4 X2 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b8e13 X0 x X2 X4
               have i₂ := b8e13 X0 x X2 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) X2) X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 X0 X3 X4 (M.op x X2)
               have i₂ := b8e13 X0 x X2 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e67 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 X2)) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (σ X0) X1 X2 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e13
            | exact resolve b8e13 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e82 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (M.op (σ X0) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e34 (σ X0) X1 X2 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e34
            | exact resolve b8e34 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e263 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (M.op (M.op X1 X2) X3) (σ X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e36 X1 X2 X3 (σ X0) (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e36
            | exact resolve b8e36 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e701 : ∀ X0 X1 X3 X4 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op (M.op (σ X0) X3) X4) X1) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b8e36 (σ X0) X3 X4 x X1
               have i₂ := b8e67 X0 x X1
               grind)
            | exact superpose b8e67 b8e36
            | exact resolve b8e36 b8e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36 b8e67
          have b8e1601 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e62 x y
               grind)
            | exact superpose b8e62 b8e20
            | (have j1 := b8e62 x y
               grind)
            | exact resolve b8e20 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1634 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e62 y x
               grind)
            | exact superpose b8e62 b8e24
            | (have j1 := b8e62 y x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e62 y x
               grind)
            | exact resolve b8e24 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e1668 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
          clear b8e1634
          have b8e1673 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e1668
               have r₂ := b8e23
               grind)
            | exact resolve b8e1668 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1668
          have b8e1677 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e1601
               have r₂ := b8e23
               grind)
            | exact resolve b8e1601 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1601
          have b8e1687 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1677
               have i₂ := b8e1673
               grind)
            | exact superpose b8e1673 b8e1677
            | exact resolve b8e1677 b8e1673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1677
          have b8e1692 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ (k x y)) X0) := by
            intro X0
            first
            | (have i₁ := b8e82 y (σ x) X0
               have i₂ := b8e1673
               grind)
            | exact superpose b8e1673 b8e82
            | exact resolve b8e82 b8e1673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e1694 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ (k x y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (σ y) X0 X1 (σ x)
               have i₂ := b8e1673
               grind)
            | exact superpose b8e1673 b8e13
            | exact resolve b8e13 b8e1673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1673
          have b8e2831 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ (M.op y x)) X0) ∨ y = (M.op x y) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b8e1692 X0
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1692
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1692 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1692
          have b8e2967 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ (M.op y x)) X0) ∨ x = y := by
            intro X0
            first
            | (have j0 := b8e2831 X0
               grind)
            | (have r₁ := b8e2831 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e2831 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2831
          have b8e2996 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ (M.op y x)) X0) := by
            intro X0
            first
            | (have j0 := b8e2967 X0
               grind)
            | (have r₁ := b8e2967 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e2967 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2967
          have b8e3085 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ (M.op y x)) X1) ∨ y = (M.op x y) ∨ x = y := by
            intro X0 X1
            first
            | (have i₁ := b8e1694 X0 X1
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1694
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1694 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1694
          have b8e3297 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ (M.op y x)) X1) ∨ x = y := by
            intro X0 X1
            first
            | (have j0 := b8e3085 X0 X1
               grind)
            | (have r₁ := b8e3085 X0 X1
               have r₂ := b8e22
               grind)
            | exact resolve b8e3085 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3085
          have b8e3395 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ (M.op y x)) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e3297 X0 X1
               grind)
            | (have r₁ := b8e3297 X0 X1
               have r₂ := b8e21
               grind)
            | exact resolve b8e3297 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3297
          have b8e19131 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e1687
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1687
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e1687
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e1687
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e1687 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1687
          have b8e19132 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) ∨ x = y := by grind
          clear b8e19131
          have b8e19133 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b8e19132
               have r₂ := b8e21
               grind)
            | exact resolve b8e19132 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19132
          have b8e19139 : (k x y) = (τ (σ x)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e14 (k x y)
               have i₂ := b8e19133
               grind)
            | exact superpose b8e19133 b8e14
            | exact resolve b8e14 b8e19133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19133
          have b8e19191 : x = (k x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e19139
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e19139
            | exact resolve b8e19139 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19139
          have b8e20249 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e18 x y
               have i₂ := b8e19191
               grind)
            | exact superpose b8e19191 b8e18
            | (have j0 := b8e18 y x
               grind)
            | exact resolve b8e18 b8e19191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19191
          have b8e20250 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e20249
          have b8e20253 : x = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b8e20250
               have r₂ := b8e22
               grind)
            | exact resolve b8e20250 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20250
          have b8e20256 : x = (M.op y x) := by
            first
            | (have r₁ := b8e20253
               have r₂ := b8e21
               grind)
            | exact resolve b8e20253 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20253
          have b8e21394 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e2996 X0
               have i₂ := b8e20256
               grind)
            | exact superpose b8e20256 b8e2996
            | exact resolve b8e2996 b8e20256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2996
          have b8e21395 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 y X0 X1 x
               have i₂ := b8e20256
               grind)
            | exact superpose b8e20256 b8e13
            | exact resolve b8e13 b8e20256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e21401 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e34 y X0 X1 x
               have i₂ := b8e20256
               grind)
            | exact superpose b8e20256 b8e34
            | exact resolve b8e34 b8e20256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34
          have b8e21453 : (M.op (σ y) x) = (M.op (σ x) x) := by
            first
            | (have i₁ := b8e3395 y x
               have i₂ := b8e20256
               grind)
            | exact superpose b8e20256 b8e3395
            | exact resolve b8e3395 b8e20256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3395 b8e20256
          have b8e27726 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op y X1) (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 x x X0 y X2 X1
               have i₂ := b8e21395 (M.op x x) X0
               grind)
            | exact superpose b8e21395 b8e32
            | exact resolve b8e32 b8e21395
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32 b8e21395
          have b8e27838 : ∀ X0 X2 : G, (M.op x X0) = (M.op x (M.op X2 X0)) := by
            intro X0 X2
            first
            | (have i₁ := b8e27726 X0 x X2
               have i₂ := b8e21401 x (M.op X2 X0)
               grind)
            | exact superpose b8e21401 b8e27726
            | exact resolve b8e27726 b8e21401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27726
          have b8e34415 : ∀ X0 X1 : G, (M.op (σ x) (σ (M.op X0 X0))) = (M.op (M.op (M.op (σ y) x) X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e263 X0 (σ x) x X1
               have i₂ := b8e21453
               grind)
            | exact superpose b8e21453 b8e263
            | exact resolve b8e263 b8e21453
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e263 b8e21453
          have b8e34453 : ∀ X0 : G, (M.op (σ (M.op y y)) (σ X0)) = (M.op (σ x) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e34415 X0 x
               have i₂ := b8e701 y (σ X0) x x
               grind)
            | exact superpose b8e701 b8e34415
            | exact resolve b8e34415 b8e701
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e701 b8e34415
          have b8e34494 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (σ x) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e34453 X0
               have i₂ := b8e21394 (σ X0)
               grind)
            | exact superpose b8e21394 b8e34453
            | exact resolve b8e34453 b8e21394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34453
          have b8e49593 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b8e30 (M.op y y)
               have i₂ := b8e21394 (σ (M.op y y))
               grind)
            | exact superpose b8e21394 b8e30
            | exact resolve b8e30 b8e21394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e21394
          have b8e49941 : (M.op (σ x) (σ y)) = (σ (M.op (M.op y y) (M.op y y))) := by
            first
            | (have i₁ := b8e49593
               have i₂ := b8e34494 y
               grind)
            | exact superpose b8e34494 b8e49593
            | exact resolve b8e49593 b8e34494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34494 b8e49593
          have b8e50116 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op y y))) := by
            first
            | (have i₁ := b8e49941
               have i₂ := b8e21401 y (M.op y y)
               grind)
            | exact superpose b8e21401 b8e49941
            | exact resolve b8e49941 b8e21401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21401 b8e49941
          have b8e50271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e50116
               have i₂ := b8e27838 y y
               grind)
            | exact superpose b8e27838 b8e50116
            | exact resolve b8e50116 b8e27838
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27838 b8e50116
          have b8e50387 : False := by grind
          exact b8e50387

/-- `Equation4535`: `x ◇ (y ◇ z) = (y ◇ w) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_y_pxy_Equation4535 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4535 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4535.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
          intro X0 X1 X2 X3
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op y x) := by grind
        have b0e21 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b0e22 : x = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e19
          | exact resolve b0e19 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e30 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X0 x y X1
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e30 X0 y
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e30
          | exact resolve b0e30 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e30
        have b0e101 : x = (M.op y x) := by
          first
          | (have i₁ := b0e22
             have i₂ := b0e41 y
             grind)
          | exact superpose b0e41 b0e22
          | exact resolve b0e22 b0e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41
        have b0e108 : x = y := by
          first
          | (have i₁ := b0e101
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e101
          | exact resolve b0e101 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e101
        have b0e145 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e21
             have i₂ := b0e108
             grind)
          | exact superpose b0e108 b0e21
          | exact resolve b0e21 b0e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e147 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e24
             have i₂ := b0e108
             grind)
          | exact superpose b0e108 b0e24
          | exact resolve b0e24 b0e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24 b0e108
        have b0e152 : False := by grind
        exact b0e152
      · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b1e21 : y = (M.op y x) := by grind
          have b1e23 : x ≠ (M.op x y) := by grind
          have b1e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e35 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X0 y x X1
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e13
            | exact resolve b1e13 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e47 : ∀ X0 : G, (M.op X0 y) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b1e35 X0 y
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e35
            | exact resolve b1e35 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e35
          have b1e157 : x ≠ (M.op y y) := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e47 y
               grind)
            | exact superpose b1e47 b1e23
            | exact resolve b1e23 b1e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e47
          have b1e166 : False := by grind
          exact b1e166
        · have b2e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op y x) := by grind
          have b2e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e34 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X0 (σ y) (σ x) X1
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e13
            | exact resolve b2e13 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e35 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X0 y x X1
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e41 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X0 y X1 x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e44 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b2e35 X0 x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e35
            | exact resolve b2e35 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e92 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X1 X0 y X2
               have i₂ := b2e44 X0
               grind)
            | (have i₁ := b2e13 X0 y X0 x
               have i₂ := b2e44 X0
               grind)
            | exact superpose b2e44 b2e13
            | exact resolve b2e13 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e96 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e35 X1 X0
               have i₂ := b2e44 X0
               grind)
            | (have i₁ := b2e35 X0 y
               have i₂ := b2e44 y
               grind)
            | exact superpose b2e44 b2e35
            | exact resolve b2e35 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e35
          have b2e103 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e92 X0 X1 X2
               have i₂ := b2e41 X1 X0
               grind)
            | exact superpose b2e41 b2e92
            | exact resolve b2e92 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e41 b2e92
          have b2e301 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b2e34 X0 (σ x)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e34
            | exact resolve b2e34 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e302 : ∀ X0 X1 X3 : G, (M.op X3 (σ y)) = (M.op (M.op (M.op X0 X1) (σ y)) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b2e34 X3 (M.op X0 x)
               have i₂ := b2e13 (σ y) X0 x X1
               grind)
            | exact superpose b2e13 b2e34
            | exact resolve b2e34 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e317 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e96 (σ y) X0
               have i₂ := b2e34 X0 y
               grind)
            | exact superpose b2e34 b2e96
            | exact resolve b2e96 b2e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e34 b2e96
          have b2e350 : ∀ X3 : G, (M.op y X3) = (M.op X3 (σ y)) := by
            intro X3
            first
            | (have i₁ := b2e302 x x X3
               have i₂ := b2e103 (M.op x x) X3 (σ y)
               grind)
            | exact superpose b2e103 b2e302
            | exact resolve b2e302 b2e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e103 b2e302
          have b2e351 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b2e301 X0
               have i₂ := b2e317 X0
               grind)
            | exact superpose b2e317 b2e301
            | exact resolve b2e301 b2e317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e301 b2e317
          have b2e396 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e350 (σ x)
               grind)
            | exact superpose b2e350 b2e20
            | exact resolve b2e20 b2e350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e350
          have b2e402 : (M.op y (σ x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b2e396
               have i₂ := b2e44 x
               grind)
            | exact superpose b2e44 b2e396
            | exact resolve b2e396 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e396
          have b2e416 : (σ y) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b2e402
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e402
            | exact resolve b2e402 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e402
          have b2e728 : (σ y) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e22
               have i₂ := b2e351 (σ x)
               grind)
            | exact superpose b2e351 b2e22
            | exact resolve b2e22 b2e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e351
          have b2e759 : (σ y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b2e728
               have i₂ := b2e44 (σ x)
               grind)
            | exact superpose b2e44 b2e728
            | exact resolve b2e728 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e44 b2e728
          have b2e773 : False := by grind
          exact b2e773
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : y = (M.op y x) := by grind
          have b3e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b3e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e20
            | exact resolve b3e20 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e36 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b3e13 X0 x y X1
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e47 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b3e36 X0 y
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e36
            | exact resolve b3e36 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e36
          have b3e194 : y = (M.op x y) := by
            first
            | (have i₁ := b3e21
               have i₂ := b3e47 y
               grind)
            | exact superpose b3e47 b3e21
            | exact resolve b3e21 b3e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e47
          have b3e206 : x = y := by
            first
            | (have i₁ := b3e194
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e194
            | exact resolve b3e194 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e194
          have b3e292 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e26
               have i₂ := b3e206
               grind)
            | exact superpose b3e206 b3e26
            | exact resolve b3e26 b3e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26
          have b3e299 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e292
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e292
            | exact resolve b3e292 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e292
          have b3e303 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e299
               have i₂ := b3e206
               grind)
            | exact superpose b3e206 b3e299
            | exact resolve b3e299 b3e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e206 b3e299
          have b3e304 : False := by grind
          exact b3e304
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b4e22 : y = (M.op y x) := by grind
            have b4e25 : x ≠ (M.op x y) := by grind
            have b4e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e33 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
              intro X0 X1
              first
              | (have i₁ := b4e14 X0 y x X1
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e14
              | exact resolve b4e14 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e45 : ∀ X0 : G, (M.op X0 y) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b4e33 X0 y
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e33
              | exact resolve b4e33 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e33
            have b4e156 : x ≠ (M.op y y) := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e45 y
                 grind)
              | exact superpose b4e45 b4e25
              | exact resolve b4e25 b4e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e45
            have b4e165 : False := by grind
            exact b4e165
          · have b5e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b5e22 : y = (M.op y x) := by grind
            have b5e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b5e25 : x ≠ (M.op x y) := by grind
            have b5e26 : x ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b5e20 X1 (τ X0)
                 have i₂ := b5e16 X0
                 grind)
              | exact superpose b5e16 b5e20
              | exact resolve b5e20 b5e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e32 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op X0 (σ y)) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X0 (σ x) (σ x) X1
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e14
              | exact resolve b5e14 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e33 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X0 y x X1
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e34 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
              intro X0 X1 X2 X4
              first
              | (have i₁ := b5e14 X2 X0 x X4
                 have i₂ := b5e14 X2 X0 x X1
                 grind)
              | (have i₁ := b5e14 (M.op X1 x) X1 X2 x
                 have i₂ := b5e14 (M.op X1 X2) X1 X2 x
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e38 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op (σ y) X0) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X0 (σ x) X1 (σ x)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e14
              | exact resolve b5e14 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e39 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y X0) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X0 y X1 x
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e41 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X4) (M.op X2 X5)) := by
              intro X0 X1 X2 X3 X4 X5
              first
              | (have i₁ := b5e14 (M.op X0 X1) X2 X3 X5
                 have i₂ := b5e14 (M.op X2 X5) X0 X1 X4
                 grind)
              | (have i₁ := b5e14 X0 X1 X2 X3
                 have i₂ := b5e14 X0 X1 X2 X3
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e42 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b5e33 X0 x
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e33
              | exact resolve b5e33 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X0 X0) = (k X0 (M.op X1 X3)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e17 X0 (M.op X1 X3)
                 have i₂ := b5e14 X0 X1 X2 X3
                 grind)
              | (have i₁ := b5e17 (M.op X1 X2) X0
                 have i₂ := b5e14 X0 X1 X2 X3
                 grind)
              | exact superpose b5e14 b5e17
              | (have j0 := b5e17 X0 (M.op X1 X3)
                 grind)
              | (have r₁ := b5e17 X0 (M.op X0 (M.op X0 X2))
                 have r₂ := b5e14 X0 X0 X2 (M.op X0 X2)
                 grind)
              | exact resolve b5e17 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e71 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e14 X1 X2 X3 X2
                 have i₂ := b5e19 X2 X0
                 grind)
              | (have i₁ := b5e14 X0 X1 X2 X3
                 have i₂ := b5e19 X0 (M.op X1 X3)
                 grind)
              | exact superpose b5e19 b5e14
              | (have j1 := b5e19 X2 X0
                 grind)
              | exact resolve b5e14 b5e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e73 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op (M.op X1 X3) (M.op X1 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e14 (M.op X1 X2) X1 X2 X3
                 have i₂ := b5e19 (M.op X1 X2) X0
                 grind)
              | (have i₁ := b5e14 X0 X1 X2 X3
                 have i₂ := b5e19 X0 (M.op X0 (M.op X1 X2))
                 grind)
              | exact superpose b5e19 b5e14
              | (have j1 := b5e19 (M.op X1 X2) X0
                 grind)
              | exact resolve b5e14 b5e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e88 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e14 X1 X0 X2 y
                 have i₂ := b5e42 X0
                 grind)
              | (have i₁ := b5e14 X0 y X2 X0
                 have i₂ := b5e42 X0
                 grind)
              | exact superpose b5e42 b5e14
              | exact resolve b5e14 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e89 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X0 X2) X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e14 X1 X0 y X2
                 have i₂ := b5e42 X0
                 grind)
              | (have i₁ := b5e14 X0 y X0 x
                 have i₂ := b5e42 X0
                 grind)
              | exact superpose b5e42 b5e14
              | exact resolve b5e14 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e92 : x ≠ (M.op y x) := by
              first
              | (have i₁ := b5e25
                 have i₂ := b5e42 x
                 grind)
              | exact superpose b5e42 b5e25
              | exact resolve b5e25 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e93 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b5e33 X1 X0
                 have i₂ := b5e42 X0
                 grind)
              | (have i₁ := b5e33 X0 y
                 have i₂ := b5e42 y
                 grind)
              | exact superpose b5e42 b5e33
              | exact resolve b5e33 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e96 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op y X2) X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e14 X1 y X0 X2
                 have i₂ := b5e42 X0
                 grind)
              | (have i₁ := b5e14 X0 X0 y x
                 have i₂ := b5e42 X0
                 grind)
              | exact superpose b5e42 b5e14
              | exact resolve b5e14 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e97 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op X0 y)) := by
              intro X0 X1
              first
              | (have i₁ := b5e96 X0 X1 x
                 have i₂ := b5e33 X1 x
                 grind)
              | exact superpose b5e33 b5e96
              | exact resolve b5e96 b5e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e96
            have b5e99 : x ≠ y := by
              first
              | (have i₁ := b5e92
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e92
              | exact resolve b5e92 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e92
            have b5e100 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op X0 X2) X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e89 X0 X1 X2
                 have i₂ := b5e39 X1 X0
                 grind)
              | exact superpose b5e39 b5e89
              | exact resolve b5e89 b5e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e89
            have b5e101 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e88 X0 X1 X2
                 have i₂ := b5e33 X1 X0
                 grind)
              | exact superpose b5e33 b5e88
              | exact resolve b5e88 b5e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e33 b5e88
            have b5e103 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e107 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 := by
              intro X0 X1
              first
              | (have j0 := b5e103 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e103
            have b5e258 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b5e15 (k X0 (τ X1))
                 have i₂ := b5e29 X1 X0
                 grind)
              | exact superpose b5e29 b5e15
              | exact resolve b5e15 b5e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e271 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (M.op X1 X2) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e14 X0 X1 y X2
                 have i₂ := b5e97 X1 X0
                 grind)
              | exact superpose b5e97 b5e14
              | exact resolve b5e14 b5e97
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e97
            have b5e307 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b5e32 X0 (σ x)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e32
              | exact resolve b5e32 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e308 : ∀ X0 X1 X3 : G, (M.op X3 (σ y)) = (M.op (M.op (M.op X0 X1) (σ x)) X3) := by
              intro X0 X1 X3
              first
              | (have i₁ := b5e32 X3 (M.op X0 x)
                 have i₂ := b5e14 (σ x) X0 x X1
                 grind)
              | exact superpose b5e14 b5e32
              | exact resolve b5e32 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e323 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b5e93 (σ x) X0
                 have i₂ := b5e32 X0 y
                 grind)
              | exact superpose b5e32 b5e93
              | exact resolve b5e93 b5e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e32 b5e93
            have b5e356 : ∀ X3 : G, (M.op y X3) = (M.op X3 (σ y)) := by
              intro X3
              first
              | (have i₁ := b5e308 x x X3
                 have i₂ := b5e100 (M.op x x) X3 (σ x)
                 grind)
              | exact superpose b5e100 b5e308
              | exact resolve b5e308 b5e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e308
            have b5e357 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b5e307 X0
                 have i₂ := b5e323 X0
                 grind)
              | exact superpose b5e323 b5e307
              | exact resolve b5e307 b5e323
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e307
            have b5e396 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ (M.op (σ y) (σ y)) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b5e17 (σ y) X0
                 have i₂ := b5e356 X0
                 grind)
              | exact superpose b5e356 b5e17
              | (have j0 := b5e17 (σ y) X0
                 grind)
              | exact resolve b5e17 b5e356
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e403 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
              first
              | (have i₁ := b5e21
                 have i₂ := b5e356 (σ x)
                 grind)
              | exact superpose b5e356 b5e21
              | exact resolve b5e21 b5e356
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e356
            have b5e409 : (M.op y (σ x)) ≠ (σ (M.op y x)) := by
              first
              | (have i₁ := b5e403
                 have i₂ := b5e42 x
                 grind)
              | exact superpose b5e42 b5e403
              | exact resolve b5e403 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e403
            have b5e416 : ∀ X0 : G, (M.op (σ y) y) = (k (σ y) X0) ∨ (M.op y X0) ≠ X0 := by
              intro X0
              first
              | (have i₁ := b5e396 X0
                 have i₂ := b5e357 (σ y)
                 grind)
              | exact superpose b5e357 b5e396
              | (have j0 := b5e396 X0
                 grind)
              | exact resolve b5e396 b5e357
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e396
            have b5e423 : (σ y) ≠ (M.op y (σ x)) := by
              first
              | (have i₁ := b5e409
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e409
              | exact resolve b5e409 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e409
            have b5e424 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ (M.op y y) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b5e416 X0
                 have i₂ := b5e357 y
                 grind)
              | exact superpose b5e357 b5e416
              | (have j0 := b5e416 X0
                 grind)
              | exact resolve b5e416 b5e357
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e416
            have b5e459 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 X2) X3) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e34 X1 X2 X3 X1
                 have i₂ := b5e19 X1 X0
                 grind)
              | (have i₁ := b5e34 X0 X1 X2 x
                 have i₂ := b5e19 X0 (M.op X0 x)
                 grind)
              | exact superpose b5e19 b5e34
              | (have j1 := b5e19 X1 X0
                 grind)
              | exact resolve b5e34 b5e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e34
            have b5e558 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X3) = (M.op y X3) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X3
              first
              | (have i₁ := b5e459 X0 X1 x X3
                 have i₂ := b5e100 X1 X3 x
                 grind)
              | exact superpose b5e100 b5e459
              | (have j0 := b5e459 X0 X1 x X3
                 grind)
              | exact resolve b5e459 b5e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e459
            have b5e628 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) X2) X0) := by
              intro X0 X2
              first
              | (have i₁ := b5e14 X0 (σ x) x X2
                 have i₂ := b5e38 X0 x
                 grind)
              | exact superpose b5e38 b5e14
              | exact resolve b5e14 b5e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e661 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b5e628 X0 x
                 have i₂ := b5e100 (σ x) X0 x
                 grind)
              | exact superpose b5e100 b5e628
              | exact resolve b5e628 b5e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e628
            have b5e4956 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b5e107 X1 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e107
            have b5e5072 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X1))) := by
              intro X0 X1
              first
              | (have j0 := b5e55 X0 X0 x (M.op X0 X1)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e55
            have b5e5073 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b5e5072 X0 x
                 have i₂ := b5e101 X0 X0 x
                 grind)
              | exact superpose b5e101 b5e5072
              | exact resolve b5e5072 b5e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e5072
            have b5e5272 : (M.op (σ y) (σ y)) = (k (σ y) (M.op y y)) := by
              first
              | (have i₁ := b5e5073 (σ y)
                 have i₂ := b5e357 y
                 grind)
              | exact superpose b5e357 b5e5073
              | exact resolve b5e5073 b5e357
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e5073
            have b5e5279 : (M.op (σ y) y) = (k (σ y) (M.op y y)) := by
              first
              | (have i₁ := b5e5272
                 have i₂ := b5e357 (σ y)
                 grind)
              | exact superpose b5e357 b5e5272
              | exact resolve b5e5272 b5e357
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e5272
            have b5e5294 : (M.op y y) = (k (σ y) (M.op y y)) := by
              first
              | (have i₁ := b5e5279
                 have i₂ := b5e357 y
                 grind)
              | exact superpose b5e357 b5e5279
              | exact resolve b5e5279 b5e357
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e5279
            have b5e5905 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e19 X0 X3
                 have i₂ := b5e71 X0 X0 X1 X2
                 grind)
              | (have i₁ := b5e19 (M.op X2 X3) X1
                 have i₂ := b5e71 X0 (M.op X2 X3) X2 X3
                 grind)
              | exact superpose b5e71 b5e19
              | (have j0 := b5e19 X0 X3
                 have j1 := b5e71 X3 X1 X0 X3
                 grind)
              | exact resolve b5e19 b5e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e6056 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X2
              first
              | (have j0 := b5e71 X0 X1 X1 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e71
            have b5e6059 : ∀ X0 X1 : G, (M.op X1 y) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b5e6056 X0 X1 x
                 have i₂ := b5e101 X1 X1 x
                 grind)
              | exact superpose b5e101 b5e6056
              | (have j0 := b5e6056 X0 X1 x
                 grind)
              | (have r₁ := b5e6056 (M.op X0 y) X0 x
                 have r₂ := b5e101 X0 X0 x
                 grind)
              | exact resolve b5e6056 b5e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e6056
            have b5e6174 : ∀ X0 X1 X3 : G, (M.op X0 y) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X3
              first
              | (have i₁ := b5e5905 X0 X1 x X3
                 have i₂ := b5e101 X1 X0 x
                 grind)
              | exact superpose b5e101 b5e5905
              | (have j0 := b5e5905 X0 X1 x X3
                 grind)
              | exact resolve b5e5905 b5e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e5905
            have b5e6313 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X3
              first
              | (have j0 := b5e6174 X0 X1 X3
                 have j1 := b5e6059 X0 X1
                 grind)
              | (have r₁ := b5e6174 X1 X1 X0
                 have r₂ := b5e6059 X0 X1
                 grind)
              | (have r₁ := b5e6174 X0 X1 (M.op X1 y)
                 have r₂ := b5e6059 (M.op X0 y) X1
                 grind)
              | (have r₁ := b5e6174 X1 X1 y
                 have r₂ := b5e6059 (k X1 y) X1
                 grind)
              | exact resolve b5e6174 b5e6059
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e6174
            have b5e6463 : (τ (M.op y y)) = (k y (τ (M.op y y))) := by
              first
              | (have i₁ := b5e258 y (M.op y y)
                 have i₂ := b5e5294
                 grind)
              | exact superpose b5e5294 b5e258
              | exact resolve b5e258 b5e5294
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e258 b5e5294
            have b5e8194 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (σ y)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e73 X0 (σ x) (σ x) x
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e73
              | exact resolve b5e73 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e8201 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e73 X0 y x x
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e73
              | exact resolve b5e73 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e73
            have b5e8409 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e8201 X0 X1
                 have i₂ := b5e42 (M.op y X0)
                 grind)
              | exact superpose b5e42 b5e8201
              | (have j0 := b5e8201 X0 X1
                 grind)
              | exact resolve b5e8201 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e8201
            have b5e8416 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) y) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e8194 X0 X1
                 have i₂ := b5e323 (M.op (σ x) X0)
                 grind)
              | exact superpose b5e323 b5e8194
              | (have j0 := b5e8194 X0 X1
                 grind)
              | exact resolve b5e8194 b5e323
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e8194
            have b5e8599 : ∀ X1 : G, (M.op y y) = X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
              intro X1
              first
              | (have i₁ := b5e8409 x X1
                 have i₂ := b5e39 y x
                 grind)
              | exact superpose b5e39 b5e8409
              | (have j0 := b5e8409 x X1
                 grind)
              | exact resolve b5e8409 b5e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e8409
            have b5e8603 : ∀ X0 X1 : G, (M.op y (M.op (σ x) X0)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e8416 X0 X1
                 have i₂ := b5e42 (M.op (σ x) X0)
                 grind)
              | exact superpose b5e42 b5e8416
              | (have j0 := b5e8416 X0 X1
                 grind)
              | exact resolve b5e8416 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e8416
            have b5e8783 : ∀ X1 : G, (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
              intro X1
              first
              | (have j0 := b5e8599 X1
                 have j1 := b5e6059 X1 y
                 grind)
              | (have r₁ := b5e8599 x
                 have r₂ := b5e6059 x y
                 grind)
              | (have r₁ := b5e8599 (M.op X1 y)
                 have r₂ := b5e6059 (M.op y y) X1
                 grind)
              | (have r₁ := b5e8599 y
                 have r₂ := b5e6059 (k y y) y
                 grind)
              | exact resolve b5e8599 b5e6059
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e8599
            have b5e8787 : ∀ X1 : G, (M.op (σ y) y) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X1
              first
              | (have i₁ := b5e8603 x X1
                 have i₂ := b5e38 y x
                 grind)
              | exact superpose b5e38 b5e8603
              | (have j0 := b5e8603 x X1
                 grind)
              | exact resolve b5e8603 b5e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e38 b5e8603
            have b5e8951 : ∀ X1 : G, (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X1
              first
              | (have j0 := b5e8787 X1
                 have j1 := b5e6059 X1 (σ y)
                 grind)
              | (have r₁ := b5e8787 x
                 have r₂ := b5e6059 x (σ y)
                 grind)
              | (have r₁ := b5e8787 (M.op X1 y)
                 have r₂ := b5e6059 (M.op (σ y) y) X1
                 grind)
              | (have r₁ := b5e8787 y
                 have r₂ := b5e6059 (k (σ y) y) (σ y)
                 grind)
              | exact resolve b5e8787 b5e6059
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e6059 b5e8787
            have b5e9089 : ∀ X1 : G, (M.op X1 y) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X1
              first
              | (have i₁ := b5e8951 X1
                 have i₂ := b5e357 X1
                 grind)
              | exact superpose b5e357 b5e8951
              | (have j0 := b5e8951 X1
                 grind)
              | exact resolve b5e8951 b5e357
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e357 b5e8951
            have b5e9188 : ∀ X1 : G, (M.op X1 y) = (k (σ y) X1) ∨ (M.op X1 y) = X1 := by
              intro X1
              first
              | (have i₁ := b5e9089 X1
                 have i₂ := b5e323 X1
                 grind)
              | exact superpose b5e323 b5e9089
              | (have j0 := b5e9089 X1
                 grind)
              | exact resolve b5e9089 b5e323
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e9089
            have b5e11391 : ∀ X0 : G, (σ (M.op (τ X0) y)) = (k (σ (σ y)) X0) ∨ (τ X0) = (M.op (τ X0) y) := by
              intro X0
              first
              | (have i₁ := b5e29 X0 (σ y)
                 have i₂ := b5e9188 (τ X0)
                 grind)
              | exact superpose b5e9188 b5e29
              | (have j1 := b5e9188 (τ X0)
                 grind)
              | exact resolve b5e29 b5e9188
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e29 b5e9188
            have b5e11397 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k (σ (σ y)) X0) ∨ (τ X0) = (M.op (τ X0) y) := by
              intro X0
              first
              | (have i₁ := b5e11391 X0
                 have i₂ := b5e42 (τ X0)
                 grind)
              | exact superpose b5e42 b5e11391
              | (have j0 := b5e11391 X0
                 grind)
              | exact resolve b5e11391 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e11391
            have b5e11407 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k (σ (σ y)) X0) ∨ (τ X0) = (M.op y (τ X0)) := by
              intro X0
              first
              | (have i₁ := b5e11397 X0
                 have i₂ := b5e42 (τ X0)
                 grind)
              | exact superpose b5e42 b5e11397
              | (have j0 := b5e11397 X0
                 grind)
              | exact resolve b5e11397 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e11397
            have b5e11980 : (τ (M.op y y)) = (M.op y (τ (M.op y y))) ∨ (τ (M.op y y)) = (M.op (τ (M.op y y)) y) := by
              first
              | (have i₁ := b5e8783 (τ (M.op y y))
                 have i₂ := b5e6463
                 grind)
              | exact superpose b5e6463 b5e8783
              | (have j0 := b5e8783 (τ (M.op y y))
                 grind)
              | exact resolve b5e8783 b5e6463
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e6463 b5e8783
            have b5e11992 : (τ (M.op y y)) = (M.op y (τ (M.op y y))) ∨ (τ (M.op y y)) = (M.op y (τ (M.op y y))) := by
              first
              | (have i₁ := b5e11980
                 have i₂ := b5e42 (τ (M.op y y))
                 grind)
              | exact superpose b5e42 b5e11980
              | exact resolve b5e11980 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e11980
            have b5e11993 : (τ (M.op y y)) = (M.op y (τ (M.op y y))) := by grind
            clear b5e11992
            have b5e12112 : ∀ X0 X1 X2 X3 : G, (M.op (M.op y X0) (M.op X1 X2)) = (M.op (τ (M.op y y)) (M.op X1 X3)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e41 y X0 X1 X2 (τ (M.op y y)) X3
                 have i₂ := b5e11993
                 grind)
              | exact superpose b5e11993 b5e41
              | exact resolve b5e41 b5e11993
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e41
            have b5e12146 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X1 X2)) = (M.op (τ (M.op y y)) y) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e12112 X0 X1 X2 x
                 have i₂ := b5e101 X1 (τ (M.op y y)) x
                 grind)
              | exact superpose b5e101 b5e12112
              | exact resolve b5e12112 b5e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e12112
            have b5e12175 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X1 X2)) = (M.op y (τ (M.op y y))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e12146 X0 X1 X2
                 have i₂ := b5e42 (τ (M.op y y))
                 grind)
              | exact superpose b5e42 b5e12146
              | exact resolve b5e12146 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e12146
            have b5e12189 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X1 X2)) = (τ (M.op y y)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e12175 X0 X1 X2
                 have i₂ := b5e11993
                 grind)
              | exact superpose b5e11993 b5e12175
              | exact resolve b5e12175 b5e11993
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e11993 b5e12175
            have b5e12200 : ∀ X0 : G, (M.op (M.op y X0) y) = (τ (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b5e12189 X0 x x
                 have i₂ := b5e101 x (M.op y X0) x
                 grind)
              | exact superpose b5e101 b5e12189
              | exact resolve b5e12189 b5e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e12189
            have b5e12203 : ∀ X0 : G, (M.op y (M.op y X0)) = (τ (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b5e12200 X0
                 have i₂ := b5e42 (M.op y X0)
                 grind)
              | exact superpose b5e42 b5e12200
              | exact resolve b5e12200 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e12200
            have b5e12205 : (M.op y y) = (τ (M.op y y)) := by
              first
              | (have i₁ := b5e12203 x
                 have i₂ := b5e39 y x
                 grind)
              | exact superpose b5e39 b5e12203
              | exact resolve b5e12203 b5e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e39 b5e12203
            have b5e12753 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ (M.op X0 (σ y)) = X0 ∨ (k (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b5e4956 (σ y) X0
                 have i₂ := b5e661 X0
                 grind)
              | exact superpose b5e661 b5e4956
              | (have j0 := b5e4956 (σ y) X0
                 grind)
              | exact resolve b5e4956 b5e661
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e661 b5e4956
            have b5e12764 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ (M.op X0 y) = X0 ∨ (k (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b5e12753 X0
                 have i₂ := b5e323 X0
                 grind)
              | exact superpose b5e323 b5e12753
              | (have j0 := b5e12753 X0
                 grind)
              | exact resolve b5e12753 b5e323
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e323 b5e12753
            have b5e15132 : ∀ X0 : G, (σ y) = (M.op y (σ x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b5e24
                 have i₂ := b5e558 (σ x) X0 (σ x)
                 grind)
              | exact superpose b5e558 b5e24
              | (have j1 := b5e558 (σ x) X0 x
                 grind)
              | exact resolve b5e24 b5e558
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e558
            have b5e15272 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have j0 := b5e15132 X0
                 grind)
              | (have r₁ := b5e15132 X0
                 have r₂ := b5e423
                 grind)
              | exact resolve b5e15132 b5e423
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e15132
            have b5e22762 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b5e6313 X0 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e6313
            have b5e22763 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b5e22762 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e22762
            have b5e22764 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b5e22763 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e22763
            have b5e22773 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b5e22764 X0
                 have j1 := b5e17 X0 X0
                 grind)
              | (have r₁ := b5e22764 X0
                 have r₂ := b5e17 X0 X0
                 grind)
              | exact resolve b5e22764 b5e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e22764
            have b5e22930 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
              intro X0
              first
              | (have i₁ := b5e20 X0 X0
                 have i₂ := b5e22773 (σ X0)
                 grind)
              | exact superpose b5e22773 b5e20
              | exact resolve b5e20 b5e22773
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e22950 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b5e22930 X0
                 have i₂ := b5e22773 X0
                 grind)
              | exact superpose b5e22773 b5e22930
              | exact resolve b5e22930 b5e22773
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e22773 b5e22930
            have b5e24669 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (M.op X0 X0)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b5e100 (σ X0) X1 (σ X0)
                 have i₂ := b5e22950 X0
                 grind)
              | exact superpose b5e22950 b5e100
              | exact resolve b5e100 b5e22950
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e100
            have b5e24670 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op X0 X0))) := by
              intro X0 X1
              first
              | (have i₁ := b5e101 (σ X0) X1 (σ X0)
                 have i₂ := b5e22950 X0
                 grind)
              | exact superpose b5e22950 b5e101
              | exact resolve b5e101 b5e22950
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e101 b5e22950
            have b5e34091 : ∀ X0 : G, (M.op y X0) = (M.op (σ (σ y)) X0) := by
              intro X0
              first
              | (have i₁ := b5e24669 (σ x) X0
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e24669
              | exact resolve b5e24669 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e24669
            have b5e36884 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ (σ y))) := by
              intro X0
              first
              | (have i₁ := b5e24670 (σ x) X0
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e24670
              | exact resolve b5e24670 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e24670
            have b5e150509 : (M.op (σ (σ y)) (σ x)) = (σ (M.op y (τ (σ x)))) ∨ (σ x) = (M.op (σ x) (σ (σ y))) ∨ (τ (σ x)) = (M.op y (τ (σ x))) := by
              first
              | (have i₁ := b5e15272 (σ (σ y))
                 have i₂ := b5e11407 (σ x)
                 grind)
              | exact superpose b5e11407 b5e15272
              | (have j0 := b5e15272 (σ (σ y))
                 have j1 := b5e11407 (σ x)
                 grind)
              | exact resolve b5e15272 b5e11407
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e11407 b5e15272
            have b5e150517 : (σ (M.op y x)) = (M.op (σ (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (σ y))) ∨ (τ (σ x)) = (M.op y (τ (σ x))) := by
              first
              | (have i₁ := b5e150509
                 have i₂ := b5e15 x
                 grind)
              | exact superpose b5e15 b5e150509
              | exact resolve b5e150509 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e150509
            have b5e150561 : (M.op y (σ x)) = (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ (σ y))) ∨ (τ (σ x)) = (M.op y (τ (σ x))) := by
              first
              | (have i₁ := b5e150517
                 have i₂ := b5e34091 (σ x)
                 grind)
              | exact superpose b5e34091 b5e150517
              | exact resolve b5e150517 b5e34091
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e34091 b5e150517
            have b5e150594 : (σ y) = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) (σ (σ y))) ∨ (τ (σ x)) = (M.op y (τ (σ x))) := by
              first
              | (have i₁ := b5e150561
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e150561
              | exact resolve b5e150561 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e150561
            have b5e150613 : (σ x) = (M.op (σ x) (σ (σ y))) ∨ (τ (σ x)) = (M.op y (τ (σ x))) := by
              first
              | (have r₁ := b5e150594
                 have r₂ := b5e423
                 grind)
              | exact resolve b5e150594 b5e423
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e423 b5e150594
            have b5e150629 : (σ x) = (M.op (σ x) y) ∨ (τ (σ x)) = (M.op y (τ (σ x))) := by
              first
              | (have i₁ := b5e150613
                 have i₂ := b5e36884 (σ x)
                 grind)
              | exact superpose b5e36884 b5e150613
              | exact resolve b5e150613 b5e36884
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e36884 b5e150613
            have b5e150638 : (σ x) = (M.op y (σ x)) ∨ (τ (σ x)) = (M.op y (τ (σ x))) := by
              first
              | (have i₁ := b5e150629
                 have i₂ := b5e42 (σ x)
                 grind)
              | exact superpose b5e42 b5e150629
              | exact resolve b5e150629 b5e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e42 b5e150629
            have b5e150647 : x = (M.op y x) ∨ (σ x) = (M.op y (σ x)) := by
              first
              | (have i₁ := b5e150638
                 have i₂ := b5e15 x
                 grind)
              | exact superpose b5e15 b5e150638
              | exact resolve b5e150638 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e150638
            have b5e150650 : x = y ∨ (σ x) = (M.op y (σ x)) := by
              first
              | (have i₁ := b5e150647
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e150647
              | exact resolve b5e150647 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e150647
            have b5e150652 : (σ x) = (M.op y (σ x)) := by
              first
              | (have r₁ := b5e150650
                 have r₂ := b5e99
                 grind)
              | exact resolve b5e150650 b5e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e99 b5e150650
            have b5e150669 : (σ x) ≠ (σ x) ∨ (M.op y y) = (k (σ y) (σ x)) := by
              first
              | (have i₁ := b5e424 (σ x)
                 have i₂ := b5e150652
                 grind)
              | exact superpose b5e150652 b5e424
              | (have j0 := b5e424 (σ x)
                 grind)
              | (have r₁ := b5e424 (σ x)
                 have r₂ := b5e150652
                 grind)
              | exact resolve b5e424 b5e150652
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e424
            have b5e150683 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) y) ∨ (σ x) = (k (σ y) (σ x)) := by
              first
              | (have i₁ := b5e12764 (σ x)
                 have i₂ := b5e150652
                 grind)
              | exact superpose b5e150652 b5e12764
              | (have j0 := b5e12764 (σ x)
                 grind)
              | (have r₁ := b5e12764 (σ x)
                 have r₂ := b5e150652
                 grind)
              | exact resolve b5e12764 b5e150652
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e12764
            have b5e150716 : ∀ X0 : G, (M.op X0 y) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b5e271 X0 y (σ x)
                 have i₂ := b5e150652
                 grind)
              | exact superpose b5e150652 b5e271
              | exact resolve b5e271 b5e150652
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e271 b5e150652
            have b5e150748 : (σ x) = (M.op (σ x) y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
            clear b5e150683
            have b5e150751 : (M.op y y) = (k (σ y) (σ x)) := by grind
            clear b5e150669
            have b5e150785 : (σ x) = (M.op y y) ∨ (σ x) = (k (σ y) (σ x)) := by
              first
              | (have i₁ := b5e150748
                 have i₂ := b5e150716 y
                 grind)
              | exact superpose b5e150716 b5e150748
              | exact resolve b5e150748 b5e150716
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e150716 b5e150748
            have b5e150791 : (M.op y y) = (σ (k y x)) := by
              first
              | (have i₁ := b5e150751
                 have i₂ := b5e20 y x
                 grind)
              | exact superpose b5e20 b5e150751
              | exact resolve b5e150751 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e150751
            have b5e150809 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op y y) := by
              first
              | (have i₁ := b5e150785
                 have i₂ := b5e20 y x
                 grind)
              | exact superpose b5e20 b5e150785
              | exact resolve b5e150785 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e150785
            have b5e150822 : (σ x) = (M.op y y) ∨ (σ x) = (M.op y y) := by
              first
              | (have i₁ := b5e150809
                 have i₂ := b5e150791
                 grind)
              | exact superpose b5e150791 b5e150809
              | exact resolve b5e150809 b5e150791
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e150791 b5e150809
            have b5e150823 : (σ x) = (M.op y y) := by grind
            clear b5e150822
            have b5e151051 : x ≠ (σ x) := by
              first
              | (have i₁ := b5e26
                 have i₂ := b5e150823
                 grind)
              | exact superpose b5e150823 b5e26
              | exact resolve b5e26 b5e150823
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e151070 : (σ x) = (τ (σ x)) := by
              first
              | (have i₁ := b5e12205
                 have i₂ := b5e150823
                 grind)
              | exact superpose b5e150823 b5e12205
              | exact resolve b5e12205 b5e150823
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e12205 b5e150823
            have b5e151294 : x = (σ x) := by
              first
              | (have i₁ := b5e151070
                 have i₂ := b5e15 x
                 grind)
              | exact superpose b5e15 b5e151070
              | exact resolve b5e151070 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e151070
            have b5e151323 : False := by grind
            exact b5e151323
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e21 : y = (M.op y x) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b6e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e20
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e20
            | exact resolve b6e20 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e35 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 X0 x y X1
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e45 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b6e35 X0 y
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e35
            | exact resolve b6e35 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e35
          have b6e61 : y ≠ y ∨ (k x y) = (M.op x x) := by
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
          have b6e62 : (k x y) = (M.op x x) := by grind
          clear b6e61
          have b6e79 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e23
               have i₂ := b6e18 (σ x) X0
               grind)
            | (have i₁ := b6e23
               have i₂ := b6e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b6e18 b6e23
            | (have j1 := b6e18 (σ x) X0
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e23 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e104 : y = (M.op x y) := by
            first
            | (have i₁ := b6e21
               have i₂ := b6e45 y
               grind)
            | exact superpose b6e45 b6e21
            | exact resolve b6e21 b6e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e45
          have b6e111 : x = y := by
            first
            | (have i₁ := b6e104
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e104
            | exact resolve b6e104 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e104
          have b6e165 : x = (M.op x x) := by
            first
            | (have i₁ := b6e24
               have i₂ := b6e111
               grind)
            | exact superpose b6e111 b6e24
            | exact resolve b6e24 b6e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e111
          have b6e4864 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b6e79 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e79
          have b6e4865 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b6e4864
               have r₂ := b6e22
               grind)
            | exact resolve b6e4864 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e4864
          have b6e4866 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b6e4865
               have i₂ := b6e19 x y
               grind)
            | exact superpose b6e19 b6e4865
            | exact resolve b6e4865 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e4865
          have b6e4867 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b6e4866
               have i₂ := b6e62
               grind)
            | exact superpose b6e62 b6e4866
            | exact resolve b6e4866 b6e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e62 b6e4866
          have b6e4868 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e4867
               have i₂ := b6e165
               grind)
            | exact superpose b6e165 b6e4867
            | exact resolve b6e4867 b6e165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e165 b6e4867
          have b6e4869 : False := by grind
          exact b6e4869
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b7e22 : y = (M.op y x) := by grind
            have b7e25 : x ≠ (M.op x y) := by grind
            have b7e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e30 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X0 y x X1
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e43 : ∀ X0 : G, (M.op X0 y) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b7e30 X0 y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e30
              | exact resolve b7e30 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e30
            have b7e148 : x ≠ (M.op y y) := by
              first
              | (have i₁ := b7e25
                 have i₂ := b7e43 y
                 grind)
              | exact superpose b7e43 b7e25
              | exact resolve b7e25 b7e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e43
            have b7e157 : False := by grind
            exact b7e157
          · have b8e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b8e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b8e22 : y = (M.op y x) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b8e25 : x ≠ (M.op x y) := by grind
            have b8e26 : x ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X1 (τ X0)
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e20
              | exact resolve b8e20 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e30 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X0 y x X1
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e35 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y X0) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X0 y X1 x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e39 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X4) (M.op X2 X5)) := by
              intro X0 X1 X2 X3 X4 X5
              first
              | (have i₁ := b8e14 (M.op X0 X1) X2 X3 X5
                 have i₂ := b8e14 (M.op X2 X5) X0 X1 X4
                 grind)
              | (have i₁ := b8e14 X0 X1 X2 X3
                 have i₂ := b8e14 X0 X1 X2 X3
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e40 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b8e30 X0 x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e30
              | exact resolve b8e30 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e52 : y ≠ y ∨ (k x y) = (M.op x x) := by
              first
              | (have i₁ := b8e17 x y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e17
              | (have j0 := b8e17 x y
                 grind)
              | (have r₁ := b8e17 x y
                 have r₂ := b8e22
                 grind)
              | exact resolve b8e17 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e54 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X0 X0) = (k X0 (M.op X1 X3)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e17 X0 (M.op X1 X3)
                 have i₂ := b8e14 X0 X1 X2 X3
                 grind)
              | (have i₁ := b8e17 (M.op X1 X2) X0
                 have i₂ := b8e14 X0 X1 X2 X3
                 grind)
              | exact superpose b8e14 b8e17
              | (have j0 := b8e17 X0 (M.op X1 X3)
                 grind)
              | (have r₁ := b8e17 X0 (M.op X0 (M.op X0 X2))
                 have r₂ := b8e14 X0 X0 X2 (M.op X0 X2)
                 grind)
              | exact resolve b8e17 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e56 : (k x y) = (M.op x x) := by grind
            clear b8e52
            have b8e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X0 X1
                 have i₂ := b8e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b8e19 b8e20
              | (have j1 := b8e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b8e20 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e66 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X1 X2 X3 X2
                 have i₂ := b8e19 X2 X0
                 grind)
              | (have i₁ := b8e14 X0 X1 X2 X3
                 have i₂ := b8e19 X0 (M.op X1 X3)
                 grind)
              | exact superpose b8e19 b8e14
              | (have j1 := b8e19 X2 X0
                 grind)
              | exact resolve b8e14 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e68 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op (M.op X1 X3) (M.op X1 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 (M.op X1 X2) X1 X2 X3
                 have i₂ := b8e19 (M.op X1 X2) X0
                 grind)
              | (have i₁ := b8e14 X0 X1 X2 X3
                 have i₂ := b8e19 X0 (M.op X0 (M.op X1 X2))
                 grind)
              | exact superpose b8e19 b8e14
              | (have j1 := b8e19 (M.op X1 X2) X0
                 grind)
              | exact resolve b8e14 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e71 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e24
                 have i₂ := b8e19 (σ x) X0
                 grind)
              | (have i₁ := b8e24
                 have i₂ := b8e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b8e19 b8e24
              | (have j1 := b8e19 (σ x) X0
                 grind)
              | (have r₁ := b8e24
                 have r₂ := b8e19 (σ x) (σ y)
                 grind)
              | exact resolve b8e24 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e83 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X1 X0 X2 y
                 have i₂ := b8e40 X0
                 grind)
              | (have i₁ := b8e14 X0 y X2 X0
                 have i₂ := b8e40 X0
                 grind)
              | exact superpose b8e40 b8e14
              | exact resolve b8e14 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e84 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X0 X2) X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X1 X0 y X2
                 have i₂ := b8e40 X0
                 grind)
              | (have i₁ := b8e14 X0 y X0 x
                 have i₂ := b8e40 X0
                 grind)
              | exact superpose b8e40 b8e14
              | exact resolve b8e14 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e90 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) X1) = (M.op X1 (M.op y X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X1 y X2 X0
                 have i₂ := b8e40 X0
                 grind)
              | (have i₁ := b8e14 X0 X0 X2 y
                 have i₂ := b8e40 X0
                 grind)
              | exact superpose b8e40 b8e14
              | exact resolve b8e14 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e91 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op y X2) X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X1 y X0 X2
                 have i₂ := b8e40 X0
                 grind)
              | (have i₁ := b8e14 X0 X0 y x
                 have i₂ := b8e40 X0
                 grind)
              | exact superpose b8e40 b8e14
              | exact resolve b8e14 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e92 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op X0 y)) := by
              intro X0 X1
              first
              | (have i₁ := b8e91 X0 X1 x
                 have i₂ := b8e30 X1 x
                 grind)
              | exact superpose b8e30 b8e91
              | exact resolve b8e91 b8e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e91
            have b8e93 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e90 X0 X1 x
                 have i₂ := b8e35 X1 x
                 grind)
              | exact superpose b8e35 b8e90
              | exact resolve b8e90 b8e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e90
            have b8e95 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op X0 X2) X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e84 X0 X1 X2
                 have i₂ := b8e35 X1 X0
                 grind)
              | exact superpose b8e35 b8e84
              | exact resolve b8e84 b8e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e84
            have b8e96 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e83 X0 X1 X2
                 have i₂ := b8e30 X1 X0
                 grind)
              | exact superpose b8e30 b8e83
              | exact resolve b8e83 b8e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e30 b8e83
            have b8e237 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e15 (k X0 (τ X1))
                 have i₂ := b8e29 X1 X0
                 grind)
              | exact superpose b8e29 b8e15
              | exact resolve b8e15 b8e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e29
            have b8e250 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (M.op X1 X2) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X0 X1 y X2
                 have i₂ := b8e92 X1 X0
                 grind)
              | exact superpose b8e92 b8e14
              | exact resolve b8e14 b8e92
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e92
            have b8e461 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op y X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X0 X1 X2 y
                 have i₂ := b8e93 X1 X0
                 grind)
              | exact superpose b8e93 b8e14
              | exact resolve b8e14 b8e93
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e93
            have b8e3169 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X4) ≠ (M.op (M.op X0 X1) (M.op X2 X3)) ∨ (M.op (M.op X2 X5) (M.op X2 X5)) = (k (M.op X2 X5) (M.op X0 X4)) := by
              intro X0 X1 X2 X3 X4 X5
              first
              | (have i₁ := b8e17 (M.op X2 X5) (M.op X0 X4)
                 have i₂ := b8e39 X0 X4 X2 X5 X1 X3
                 grind)
              | (have i₁ := b8e17 (M.op X2 X5) (M.op X0 X4)
                 have i₂ := b8e39 X0 X1 X2 X3 X4 X5
                 grind)
              | exact superpose b8e39 b8e17
              | (have j0 := b8e17 (M.op X2 X5) (M.op X0 X4)
                 grind)
              | exact resolve b8e17 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e3194 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 X4) ≠ (M.op (M.op X0 X1) y) ∨ (M.op (M.op X2 X5) (M.op X2 X5)) = (k (M.op X2 X5) (M.op X0 X4)) := by
              intro X0 X1 X2 X4 X5
              first
              | (have i₁ := b8e3169 X0 X1 X2 x X4 X5
                 have i₂ := b8e96 X2 (M.op X0 X1) x
                 grind)
              | exact superpose b8e96 b8e3169
              | (have j0 := b8e3169 X0 X1 X2 x X4 X5
                 grind)
              | exact resolve b8e3169 b8e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3169
            have b8e3394 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 X4) ≠ (M.op y (M.op X0 X1)) ∨ (M.op (M.op X2 X5) (M.op X2 X5)) = (k (M.op X2 X5) (M.op X0 X4)) := by
              intro X0 X1 X2 X4 X5
              first
              | (have i₁ := b8e3194 X0 X1 X2 X4 X5
                 have i₂ := b8e40 (M.op X0 X1)
                 grind)
              | exact superpose b8e40 b8e3194
              | (have j0 := b8e3194 X0 X1 X2 X4 X5
                 grind)
              | (have r₁ := b8e3194 y X1 X2 (M.op y X1) X5
                 have r₂ := b8e40 (M.op y X1)
                 grind)
              | exact resolve b8e3194 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3194
            have b8e3573 : ∀ X0 X2 X4 X5 : G, (M.op y y) ≠ (M.op X0 X4) ∨ (M.op (M.op X2 X5) (M.op X2 X5)) = (k (M.op X2 X5) (M.op X0 X4)) := by
              intro X0 X2 X4 X5
              first
              | (have i₁ := b8e3394 X0 x X2 X4 X5
                 have i₂ := b8e96 X0 y x
                 grind)
              | exact superpose b8e96 b8e3394
              | (have j0 := b8e3394 X0 x X2 X4 X5
                 grind)
              | (have r₁ := b8e3394 y X2 X2 y X5
                 have r₂ := b8e96 y y X2
                 grind)
              | exact resolve b8e3394 b8e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3394
            have b8e3716 : ∀ X0 X2 X4 X5 : G, (M.op (M.op X2 X5) y) = (k (M.op X2 X5) (M.op X0 X4)) ∨ (M.op y y) ≠ (M.op X0 X4) := by
              intro X0 X2 X4 X5
              first
              | (have i₁ := b8e3573 X0 X2 X4 X5
                 have i₂ := b8e96 X2 (M.op X2 X5) X5
                 grind)
              | exact superpose b8e96 b8e3573
              | (have j0 := b8e3573 X0 X2 X4 X5
                 grind)
              | (have r₁ := b8e3573 y X2 (M.op X0 X2) X5
                 have r₂ := b8e96 X0 y X2
                 grind)
              | exact resolve b8e3573 b8e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3573
            have b8e3830 : ∀ X0 X2 X4 X5 : G, (M.op y (M.op X2 X5)) = (k (M.op X2 X5) (M.op X0 X4)) ∨ (M.op y y) ≠ (M.op X0 X4) := by
              intro X0 X2 X4 X5
              first
              | (have i₁ := b8e3716 X0 X2 X4 X5
                 have i₂ := b8e40 (M.op X2 X5)
                 grind)
              | exact superpose b8e40 b8e3716
              | (have j0 := b8e3716 X0 X2 X4 X5
                 grind)
              | (have r₁ := b8e3716 y X2 y X5
                 have r₂ := b8e40 y
                 grind)
              | exact resolve b8e3716 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3716
            have b8e3838 : ∀ X0 X2 X4 X5 : G, (M.op y y) ≠ (M.op X0 X4) ∨ (M.op y y) = (k (M.op X2 X5) (M.op X0 X4)) := by
              intro X0 X2 X4 X5
              first
              | (have i₁ := b8e3830 X0 X2 X4 X5
                 have i₂ := b8e96 X2 y X5
                 grind)
              | exact superpose b8e96 b8e3830
              | (have j0 := b8e3830 X0 X2 X4 X5
                 grind)
              | (have r₁ := b8e3830 y X2 (M.op X0 X2) X5
                 have r₂ := b8e96 X0 y X2
                 grind)
              | exact resolve b8e3830 b8e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3830
            have b8e3971 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X1))) := by
              intro X0 X1
              first
              | (have j0 := b8e54 X0 X0 x (M.op X0 X1)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e54
            have b8e3972 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b8e3971 X0 x
                 have i₂ := b8e96 X0 X0 x
                 grind)
              | exact superpose b8e96 b8e3971
              | exact resolve b8e3971 b8e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3971
            have b8e4193 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b8e71 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e71
            have b8e4194 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b8e4193
                 have r₂ := b8e23
                 grind)
              | exact resolve b8e4193 b8e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4193
            have b8e4195 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e4194
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e4194
              | exact resolve b8e4194 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4194
            have b8e4196 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b8e4195
                 have i₂ := b8e56
                 grind)
              | exact superpose b8e56 b8e4195
              | exact resolve b8e4195 b8e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4195
            have b8e4534 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b8e21
                 have i₂ := b8e4196
                 grind)
              | exact superpose b8e4196 b8e21
              | exact resolve b8e21 b8e4196
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e4554 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op x x)) X0) := by
              intro X0
              first
              | (have i₁ := b8e95 (σ x) X0 (σ y)
                 have i₂ := b8e4196
                 grind)
              | exact superpose b8e4196 b8e95
              | exact resolve b8e95 b8e4196
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e4557 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ (M.op x x))) := by
              intro X0
              first
              | (have i₁ := b8e461 X0 (σ x) (σ y)
                 have i₂ := b8e4196
                 grind)
              | exact superpose b8e4196 b8e461
              | exact resolve b8e461 b8e4196
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e4577 : (σ (M.op x x)) ≠ (σ (M.op y x)) := by
              first
              | (have i₁ := b8e4534
                 have i₂ := b8e40 x
                 grind)
              | exact superpose b8e40 b8e4534
              | exact resolve b8e4534 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4534
            have b8e4583 : (σ y) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b8e4577
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e4577
              | exact resolve b8e4577 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4577
            have b8e4689 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e19 X0 X3
                 have i₂ := b8e66 X0 X0 X1 X2
                 grind)
              | (have i₁ := b8e19 (M.op X2 X3) X1
                 have i₂ := b8e66 X0 (M.op X2 X3) X2 X3
                 grind)
              | exact superpose b8e66 b8e19
              | (have j0 := b8e19 X0 X3
                 have j1 := b8e66 X3 X1 X0 X3
                 grind)
              | exact resolve b8e19 b8e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e4826 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) X2) = (M.op X2 (M.op (σ X0) X3)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e20 X0 X1
                 have i₂ := b8e66 (σ X1) X2 (σ X0) X3
                 grind)
              | exact superpose b8e66 b8e20
              | (have j1 := b8e66 (σ X1) X2 (σ X0) X3
                 grind)
              | exact resolve b8e20 b8e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e4830 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X2
              first
              | (have j0 := b8e66 X0 X1 X1 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e66
            have b8e4833 : ∀ X0 X1 : G, (M.op X1 y) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b8e4830 X0 X1 x
                 have i₂ := b8e96 X1 X1 x
                 grind)
              | exact superpose b8e96 b8e4830
              | (have j0 := b8e4830 X0 X1 x
                 grind)
              | (have r₁ := b8e4830 (M.op X0 y) X0 x
                 have r₂ := b8e96 X0 X0 x
                 grind)
              | exact resolve b8e4830 b8e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4830
            have b8e4837 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op (σ X1) X2) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e4826 X0 X1 X2 x
                 have i₂ := b8e96 (σ X0) X2 x
                 grind)
              | exact superpose b8e96 b8e4826
              | (have j0 := b8e4826 X0 X1 X2 x
                 grind)
              | exact resolve b8e4826 b8e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4826
            have b8e4938 : ∀ X0 X1 X3 : G, (M.op X0 y) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X3
              first
              | (have i₁ := b8e4689 X0 X1 x X3
                 have i₂ := b8e96 X1 X0 x
                 grind)
              | exact superpose b8e96 b8e4689
              | (have j0 := b8e4689 X0 X1 x X3
                 grind)
              | exact resolve b8e4689 b8e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4689
            have b8e5059 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X3
              first
              | (have j0 := b8e4938 X0 X1 X3
                 have j1 := b8e4833 X0 X1
                 grind)
              | (have r₁ := b8e4938 X1 X1 X0
                 have r₂ := b8e4833 X0 X1
                 grind)
              | (have r₁ := b8e4938 X0 X1 (M.op X1 y)
                 have r₂ := b8e4833 (M.op X0 y) X1
                 grind)
              | (have r₁ := b8e4938 X1 X1 y
                 have r₂ := b8e4833 (k X1 y) X1
                 grind)
              | exact resolve b8e4938 b8e4833
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4938
            have b8e5259 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (k (σ (M.op x x)) (M.op y y)) := by
              first
              | (have i₁ := b8e3972 (σ (M.op x x))
                 have i₂ := b8e4554 y
                 grind)
              | exact superpose b8e4554 b8e3972
              | exact resolve b8e3972 b8e4554
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3972 b8e4554
            have b8e5264 : (M.op y (σ (M.op x x))) = (k (σ (M.op x x)) (M.op y y)) := by
              first
              | (have i₁ := b8e5259
                 have i₂ := b8e4557 (σ (M.op x x))
                 grind)
              | exact superpose b8e4557 b8e5259
              | exact resolve b8e5259 b8e4557
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e5259
            have b8e5314 : (M.op y y) = (k (σ (M.op x x)) (M.op y y)) := by
              first
              | (have i₁ := b8e5264
                 have i₂ := b8e4557 y
                 grind)
              | exact superpose b8e4557 b8e5264
              | exact resolve b8e5264 b8e4557
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4557 b8e5264
            have b8e6252 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e17 (σ X1) (σ X0)
                 have i₂ := b8e63 X1 X0
                 grind)
              | exact superpose b8e63 b8e17
              | (have j0 := b8e17 (σ X1) (σ X0)
                 have j1 := b8e63 X1 X0
                 grind)
              | (have r₁ := b8e17 (σ X1) (σ X1)
                 have r₂ := b8e63 X1 X1
                 grind)
              | (have r₁ := b8e17 (σ X0) (σ X1)
                 have r₂ := b8e63 X0 X1
                 grind)
              | exact resolve b8e17 b8e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e63
            have b8e6284 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b8e6252 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e6252
            have b8e6314 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e6284 X0 X1
                 have i₂ := b8e20 X1 X0
                 grind)
              | exact superpose b8e20 b8e6284
              | (have j0 := b8e6284 X0 X1
                 grind)
              | exact resolve b8e6284 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e6284
            have b8e7078 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b8e68 X0 y x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e68
              | exact resolve b8e68 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e7133 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) y) = X0 ∨ (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op X0 (M.op X1 X2)) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e250 (M.op X1 X2) X1 x
                 have i₂ := b8e68 X0 X1 X2 x
                 grind)
              | (have i₁ := b8e250 X0 X1 X2
                 have i₂ := b8e68 (M.op (M.op X1 X2) X0) X1 X2 x
                 grind)
              | exact superpose b8e68 b8e250
              | (have j1 := b8e68 X0 X1 X2 x
                 grind)
              | exact resolve b8e250 b8e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e68 b8e250
            have b8e7232 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op X0 (M.op X1 X2)) = X0 := by
              intro X0 X1 X2
              first
              | (have j0 := b8e7133 X0 X1 X2
                 have j1 := b8e4833 X0 (M.op X1 X2)
                 grind)
              | (have r₁ := b8e7133 X0 X1 X2
                 have r₂ := b8e4833 X0 (M.op X1 X2)
                 grind)
              | (have r₁ := b8e7133 (M.op X1 y) X1 X2
                 have r₂ := b8e4833 (M.op (M.op X1 X2) y) X1
                 grind)
              | (have r₁ := b8e7133 y X1 X2
                 have r₂ := b8e4833 (k (M.op X1 X2) y) (M.op X1 X2)
                 grind)
              | exact resolve b8e7133 b8e4833
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7133
            have b8e7273 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b8e7078 X0 X1
                 have i₂ := b8e40 (M.op y X0)
                 grind)
              | exact superpose b8e40 b8e7078
              | (have j0 := b8e7078 X0 X1
                 grind)
              | exact resolve b8e7078 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7078
            have b8e7406 : ∀ X0 X1 X2 : G, (M.op y X0) = (k (M.op X1 X2) X0) ∨ (M.op X0 (M.op X1 X2)) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e7232 X0 X1 X2
                 have i₂ := b8e95 X1 X0 X2
                 grind)
              | exact superpose b8e95 b8e7232
              | (have j0 := b8e7232 X0 X1 X2
                 grind)
              | exact resolve b8e7232 b8e95
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7232
            have b8e7445 : ∀ X1 : G, (M.op y y) = X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
              intro X1
              first
              | (have i₁ := b8e7273 x X1
                 have i₂ := b8e35 y x
                 grind)
              | exact superpose b8e35 b8e7273
              | (have j0 := b8e7273 x X1
                 grind)
              | exact resolve b8e7273 b8e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7273
            have b8e7572 : ∀ X0 X1 X2 : G, (M.op y X0) = (k (M.op X1 X2) X0) ∨ (M.op X0 y) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e7406 X0 X1 X2
                 have i₂ := b8e96 X1 X0 X2
                 grind)
              | exact superpose b8e96 b8e7406
              | (have j0 := b8e7406 X0 X1 X2
                 grind)
              | exact resolve b8e7406 b8e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7406
            have b8e7611 : ∀ X1 : G, (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
              intro X1
              first
              | (have j0 := b8e7445 X1
                 have j1 := b8e4833 X1 y
                 grind)
              | (have r₁ := b8e7445 x
                 have r₂ := b8e4833 x y
                 grind)
              | (have r₁ := b8e7445 (M.op X1 y)
                 have r₂ := b8e4833 (M.op y y) X1
                 grind)
              | (have r₁ := b8e7445 y
                 have r₂ := b8e4833 (k y y) y
                 grind)
              | exact resolve b8e7445 b8e4833
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4833 b8e7445
            have b8e11361 : (τ (M.op y y)) = (k (M.op x x) (τ (M.op y y))) := by
              first
              | (have i₁ := b8e237 (M.op x x) (M.op y y)
                 have i₂ := b8e5314
                 grind)
              | exact superpose b8e5314 b8e237
              | exact resolve b8e237 b8e5314
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e237 b8e5314
            have b8e13575 : (τ (M.op y y)) = (M.op y (τ (M.op y y))) ∨ (τ (M.op y y)) = (M.op (τ (M.op y y)) y) := by
              first
              | (have i₁ := b8e11361
                 have i₂ := b8e7572 (τ (M.op y y)) x x
                 grind)
              | exact superpose b8e7572 b8e11361
              | (have j1 := b8e7572 (τ (M.op y y)) x x
                 grind)
              | exact resolve b8e11361 b8e7572
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7572 b8e11361
            have b8e13608 : (τ (M.op y y)) = (M.op y (τ (M.op y y))) ∨ (τ (M.op y y)) = (M.op y (τ (M.op y y))) := by
              first
              | (have i₁ := b8e13575
                 have i₂ := b8e40 (τ (M.op y y))
                 grind)
              | exact superpose b8e40 b8e13575
              | exact resolve b8e13575 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e13575
            have b8e13609 : (τ (M.op y y)) = (M.op y (τ (M.op y y))) := by grind
            clear b8e13608
            have b8e14310 : ∀ X0 X1 X2 X3 : G, (M.op (M.op y X0) (M.op X1 X2)) = (M.op (τ (M.op y y)) (M.op X1 X3)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e39 y X0 X1 X2 (τ (M.op y y)) X3
                 have i₂ := b8e13609
                 grind)
              | exact superpose b8e13609 b8e39
              | exact resolve b8e39 b8e13609
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e39
            have b8e14354 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X1 X2)) = (M.op (τ (M.op y y)) y) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14310 X0 X1 X2 x
                 have i₂ := b8e96 X1 (τ (M.op y y)) x
                 grind)
              | exact superpose b8e96 b8e14310
              | exact resolve b8e14310 b8e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e14310
            have b8e14387 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X1 X2)) = (M.op y (τ (M.op y y))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14354 X0 X1 X2
                 have i₂ := b8e40 (τ (M.op y y))
                 grind)
              | exact superpose b8e40 b8e14354
              | exact resolve b8e14354 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e14354
            have b8e14403 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X1 X2)) = (τ (M.op y y)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14387 X0 X1 X2
                 have i₂ := b8e13609
                 grind)
              | exact superpose b8e13609 b8e14387
              | exact resolve b8e14387 b8e13609
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e13609 b8e14387
            have b8e14415 : ∀ X0 : G, (M.op (M.op y X0) y) = (τ (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b8e14403 X0 x x
                 have i₂ := b8e96 x (M.op y X0) x
                 grind)
              | exact superpose b8e96 b8e14403
              | exact resolve b8e14403 b8e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e96 b8e14403
            have b8e14419 : ∀ X0 : G, (M.op y (M.op y X0)) = (τ (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b8e14415 X0
                 have i₂ := b8e40 (M.op y X0)
                 grind)
              | exact superpose b8e40 b8e14415
              | exact resolve b8e14415 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e14415
            have b8e14421 : (M.op y y) = (τ (M.op y y)) := by
              first
              | (have i₁ := b8e14419 x
                 have i₂ := b8e35 y x
                 grind)
              | exact superpose b8e35 b8e14419
              | exact resolve b8e14419 b8e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e35 b8e14419
            have b8e14936 : (M.op y y) = (σ (M.op y y)) := by
              first
              | (have i₁ := b8e16 (M.op y y)
                 have i₂ := b8e14421
                 grind)
              | exact superpose b8e14421 b8e16
              | exact resolve b8e16 b8e14421
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e19686 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b8e5059 X0 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e5059
            have b8e19687 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b8e19686 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e19686
            have b8e19688 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b8e19687 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e19687
            have b8e19701 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b8e19688 X0
                 have j1 := b8e17 X0 X0
                 grind)
              | (have r₁ := b8e19688 X0
                 have r₂ := b8e17 X0 X0
                 grind)
              | exact resolve b8e19688 b8e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e19688
            have b8e19788 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
              intro X0
              first
              | (have i₁ := b8e20 X0 X0
                 have i₂ := b8e19701 (σ X0)
                 grind)
              | exact superpose b8e19701 b8e20
              | exact resolve b8e20 b8e19701
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e19800 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b8e19788 X0
                 have i₂ := b8e19701 X0
                 grind)
              | exact superpose b8e19701 b8e19788
              | exact resolve b8e19788 b8e19701
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e19701 b8e19788
            have b8e28022 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ y) y) ∨ (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b8e4196
                 have i₂ := b8e4837 X0 x (σ y)
                 grind)
              | exact superpose b8e4837 b8e4196
              | (have j1 := b8e4837 X0 x x
                 grind)
              | exact resolve b8e4196 b8e4837
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4837
            have b8e28419 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (M.op y (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e28022 X0
                 have i₂ := b8e40 (σ y)
                 grind)
              | exact superpose b8e40 b8e28022
              | (have j0 := b8e28022 X0
                 grind)
              | exact resolve b8e28022 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e28022
            have b8e35083 : (σ y) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b8e23
                 have i₂ := b8e6314 x y
                 grind)
              | exact superpose b8e6314 b8e23
              | (have j1 := b8e6314 x y
                 grind)
              | exact resolve b8e23 b8e6314
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e6314
            have b8e35240 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b8e35083
                 have i₂ := b8e19800 y
                 grind)
              | exact superpose b8e19800 b8e35083
              | exact resolve b8e35083 b8e19800
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e35083
            have b8e35567 : (M.op y y) = (σ (k y x)) ∨ (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b8e35240
                 have i₂ := b8e14936
                 grind)
              | exact superpose b8e14936 b8e35240
              | exact resolve b8e35240 b8e14936
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e35240
            have b8e35824 : (σ x) = (σ (M.op y y)) ∨ (M.op y y) = (σ (k y x)) ∨ (σ y) ≠ (σ (k y x)) := by
              first
              | (have i₁ := b8e35567
                 have i₂ := b8e19800 y
                 grind)
              | exact superpose b8e19800 b8e35567
              | exact resolve b8e35567 b8e19800
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e19800 b8e35567
            have b8e35985 : (σ y) ≠ (σ (k y x)) ∨ (M.op y y) = (σ (k y x)) ∨ (σ x) = (M.op y y) := by
              first
              | (have i₁ := b8e35824
                 have i₂ := b8e14936
                 grind)
              | exact superpose b8e14936 b8e35824
              | exact resolve b8e35824 b8e14936
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e14936 b8e35824
            have b8e155057 : (σ y) ≠ (σ (M.op y x)) ∨ (M.op y y) = (σ (M.op y x)) ∨ (σ x) = (M.op y y) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b8e35985
                 have i₂ := b8e7611 x
                 grind)
              | exact superpose b8e7611 b8e35985
              | (have j1 := b8e7611 x
                 grind)
              | exact resolve b8e35985 b8e7611
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e35985
            have b8e155061 : (σ y) ≠ (σ (M.op y x)) ∨ (M.op y y) = (σ (M.op y x)) ∨ (σ x) = (M.op y y) := by
              first
              | (have r₁ := b8e155057
                 have r₂ := b8e25
                 grind)
              | exact resolve b8e155057 b8e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155057
            have b8e155067 : (σ y) ≠ (σ y) ∨ (M.op y y) = (σ (M.op y x)) ∨ (σ x) = (M.op y y) := by
              first
              | (have i₁ := b8e155061
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e155061
              | exact resolve b8e155061 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155061
            have b8e155068 : (M.op y y) = (σ (M.op y x)) ∨ (σ x) = (M.op y y) := by grind
            clear b8e155067
            have b8e155074 : (σ x) = (M.op y y) ∨ (σ y) = (M.op y y) := by
              first
              | (have i₁ := b8e155068
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e155068
              | exact resolve b8e155068 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155068
            have b8e155084 : x ≠ (σ x) ∨ (σ y) = (M.op y y) := by
              first
              | (have i₁ := b8e26
                 have i₂ := b8e155074
                 grind)
              | exact superpose b8e155074 b8e26
              | exact resolve b8e26 b8e155074
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e155102 : (σ x) = (τ (σ x)) ∨ (σ y) = (M.op y y) := by
              first
              | (have i₁ := b8e14421
                 have i₂ := b8e155074
                 grind)
              | exact superpose b8e155074 b8e14421
              | exact resolve b8e14421 b8e155074
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155074
            have b8e155374 : x = (σ x) ∨ (σ y) = (M.op y y) := by
              first
              | (have i₁ := b8e155102
                 have i₂ := b8e15 x
                 grind)
              | exact superpose b8e15 b8e155102
              | exact resolve b8e155102 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155102
            have b8e155402 : (σ y) = (M.op y y) := by
              first
              | (have r₁ := b8e155374
                 have r₂ := b8e155084
                 grind)
              | exact resolve b8e155374 b8e155084
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155084 b8e155374
            have b8e155543 : (σ y) = (τ (σ y)) := by
              first
              | (have i₁ := b8e14421
                 have i₂ := b8e155402
                 grind)
              | exact superpose b8e155402 b8e14421
              | exact resolve b8e14421 b8e155402
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e14421
            have b8e155723 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b8e95 y X0 y
                 have i₂ := b8e155402
                 grind)
              | exact superpose b8e155402 b8e95
              | exact resolve b8e95 b8e155402
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e95
            have b8e155727 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e461 X0 y y
                 have i₂ := b8e155402
                 grind)
              | exact superpose b8e155402 b8e461
              | exact resolve b8e461 b8e155402
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e461
            have b8e155729 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (M.op X0 X1) (σ y)) := by
              intro X0 X1
              first
              | (have i₁ := b8e3838 y x y x
                 have i₂ := b8e155402
                 grind)
              | exact superpose b8e155402 b8e3838
              | exact resolve b8e3838 b8e155402
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3838
            have b8e155755 : ∀ X0 X1 : G, (σ y) = (k (M.op X0 X1) (σ y)) := by
              intro X0 X1
              first
              | (have j0 := b8e155729 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155729
            have b8e155840 : y = (σ y) := by
              first
              | (have i₁ := b8e155543
                 have i₂ := b8e15 y
                 grind)
              | exact superpose b8e15 b8e155543
              | exact resolve b8e155543 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155543
            have b8e156104 : y ≠ (M.op y (σ x)) := by
              first
              | (have i₁ := b8e23
                 have i₂ := b8e155840
                 grind)
              | exact superpose b8e155840 b8e23
              | exact resolve b8e23 b8e155840
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e156106 : (σ (M.op x x)) = (M.op (σ x) y) := by
              first
              | (have i₁ := b8e4196
                 have i₂ := b8e155840
                 grind)
              | exact superpose b8e155840 b8e4196
              | exact resolve b8e4196 b8e155840
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4196
            have b8e156216 : (σ (M.op x x)) = (M.op y (σ x)) := by
              first
              | (have i₁ := b8e156106
                 have i₂ := b8e40 (σ x)
                 grind)
              | exact superpose b8e40 b8e156106
              | exact resolve b8e156106 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e40 b8e156106
            have b8e206694 : ∀ X0 : G, (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ (σ (M.op x x)) = (M.op y (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e155755 (σ x) (σ X0)
                 have i₂ := b8e28419 X0
                 grind)
              | exact superpose b8e28419 b8e155755
              | (have j1 := b8e28419 X0
                 grind)
              | exact resolve b8e155755 b8e28419
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e28419 b8e155755
            have b8e206702 : ∀ X0 : G, (σ y) = (σ (k x y)) ∨ (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ (σ (M.op x x)) = (M.op y (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e206694 X0
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e206694
              | (have j0 := b8e206694 X0
                 grind)
              | exact resolve b8e206694 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e206694
            have b8e206731 : ∀ X0 : G, (σ y) = (σ (M.op x x)) ∨ (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ (σ (M.op x x)) = (M.op y (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e206702 X0
                 have i₂ := b8e56
                 grind)
              | exact superpose b8e56 b8e206702
              | (have j0 := b8e206702 X0
                 grind)
              | exact resolve b8e206702 b8e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e56 b8e206702
            have b8e206755 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ (σ (M.op x x)) = (M.op y (σ y)) := by
              intro X0
              first
              | (have j0 := b8e206731 X0
                 grind)
              | (have r₁ := b8e206731 X0
                 have r₂ := b8e4583
                 grind)
              | exact resolve b8e206731 b8e4583
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e4583 b8e206731
            have b8e206768 : ∀ X0 : G, (M.op y y) = (σ (M.op x x)) ∨ (M.op (σ X0) (σ x)) = (σ (k X0 x)) := by
              intro X0
              first
              | (have i₁ := b8e206755 X0
                 have i₂ := b8e155727 y
                 grind)
              | exact superpose b8e155727 b8e206755
              | (have j0 := b8e206755 X0
                 grind)
              | exact resolve b8e206755 b8e155727
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155727 b8e206755
            have b8e206773 : ∀ X0 : G, (M.op y y) = (M.op y (σ x)) ∨ (M.op (σ X0) (σ x)) = (σ (k X0 x)) := by
              intro X0
              first
              | (have i₁ := b8e206768 X0
                 have i₂ := b8e156216
                 grind)
              | exact superpose b8e156216 b8e206768
              | (have j0 := b8e206768 X0
                 grind)
              | exact resolve b8e206768 b8e156216
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e156216 b8e206768
            have b8e206777 : ∀ X0 : G, (σ y) = (M.op y (σ x)) ∨ (M.op (σ X0) (σ x)) = (σ (k X0 x)) := by
              intro X0
              first
              | (have i₁ := b8e206773 X0
                 have i₂ := b8e155402
                 grind)
              | exact superpose b8e155402 b8e206773
              | (have j0 := b8e206773 X0
                 grind)
              | exact resolve b8e206773 b8e155402
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155402 b8e206773
            have b8e206780 : ∀ X0 : G, y = (M.op y (σ x)) ∨ (M.op (σ X0) (σ x)) = (σ (k X0 x)) := by
              intro X0
              first
              | (have i₁ := b8e206777 X0
                 have i₂ := b8e155840
                 grind)
              | exact superpose b8e155840 b8e206777
              | (have j0 := b8e206777 X0
                 grind)
              | exact resolve b8e206777 b8e155840
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e206777
            have b8e206782 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) := by
              intro X0
              first
              | (have j0 := b8e206780 X0
                 grind)
              | (have r₁ := b8e206780 X0
                 have r₂ := b8e156104
                 grind)
              | exact resolve b8e206780 b8e156104
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e206780
            have b8e206893 : (σ (k y x)) = (M.op y (σ x)) := by
              first
              | (have i₁ := b8e155723 (σ x)
                 have i₂ := b8e206782 y
                 grind)
              | exact superpose b8e206782 b8e155723
              | exact resolve b8e155723 b8e206782
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155723 b8e206782
            have b8e208011 : (σ (M.op y x)) = (M.op y (σ x)) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b8e206893
                 have i₂ := b8e7611 x
                 grind)
              | exact superpose b8e7611 b8e206893
              | (have j1 := b8e7611 x
                 grind)
              | exact resolve b8e206893 b8e7611
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7611 b8e206893
            have b8e208109 : (σ (M.op y x)) = (M.op y (σ x)) := by
              first
              | (have r₁ := b8e208011
                 have r₂ := b8e25
                 grind)
              | exact resolve b8e208011 b8e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e208011
            have b8e208141 : (σ y) = (M.op y (σ x)) := by
              first
              | (have i₁ := b8e208109
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e208109
              | exact resolve b8e208109 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e208109
            have b8e208172 : y = (M.op y (σ x)) := by
              first
              | (have i₁ := b8e208141
                 have i₂ := b8e155840
                 grind)
              | exact superpose b8e155840 b8e208141
              | exact resolve b8e208141 b8e155840
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e155840 b8e208141
            have b8e208199 : False := by grind
            exact b8e208199
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b9e21 : y ≠ (M.op y x) := by grind
          have b9e22 : y = (M.op x x) := by grind
          have b9e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e43 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X0 x X1 x
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e13
            | exact resolve b9e13 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e44 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X0 x X1 y
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e13
            | exact resolve b9e13 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e47 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b9e43 X0 x
               have i₂ := b9e44 X0 x
               grind)
            | exact superpose b9e44 b9e43
            | exact resolve b9e43 b9e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e43 b9e44
          have b9e53 : y ≠ (M.op x x) := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e47 x
               grind)
            | exact superpose b9e47 b9e21
            | exact resolve b9e21 b9e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e47
          have b9e54 : False := by grind
          exact b9e54
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b10e23 : y = (M.op x x) := by grind
            have b10e25 : x ≠ (M.op x y) := by grind
            have b10e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e33 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
              intro X0 X1
              first
              | (have i₁ := b10e14 X0 x x X1
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e14
              | exact resolve b10e14 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e34 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 x) := by
              intro X0 X1
              first
              | (have i₁ := b10e14 X0 y y X1
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e14
              | exact resolve b10e14 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e44 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b10e33 X0 x
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e33
              | exact resolve b10e33 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e66 : x ≠ (M.op y x) := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e44 x
                 grind)
              | exact superpose b10e44 b10e25
              | exact resolve b10e25 b10e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e67 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y x) X0) := by
              intro X0
              first
              | (have i₁ := b10e33 X0 y
                 have i₂ := b10e44 x
                 grind)
              | exact superpose b10e44 b10e33
              | exact resolve b10e33 b10e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e33 b10e44
            have b10e81 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b10e67 X0
                 have i₂ := b10e34 X0 x
                 grind)
              | exact superpose b10e34 b10e67
              | exact resolve b10e67 b10e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e34 b10e67
            have b10e191 : x ≠ (M.op y y) := by
              first
              | (have i₁ := b10e66
                 have i₂ := b10e81 y
                 grind)
              | exact superpose b10e81 b10e66
              | exact resolve b10e66 b10e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e66 b10e81
            have b10e205 : False := by grind
            exact b10e205
          · have b11e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b11e22 : y ≠ (M.op y x) := by grind
            have b11e23 : y = (M.op x x) := by grind
            have b11e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b11e25 : x ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e32 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X0 (σ y) (σ x) X1
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e14
              | exact resolve b11e14 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e33 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X0 x x X1
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e38 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ y) X0) := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X0 (σ y) X1 (σ x)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e14
              | exact resolve b11e14 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e39 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y X0) := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X0 x X1 x
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e42 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b11e33 X0 x
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e33
              | exact resolve b11e33 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e57 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e59 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear b11e57
            have b11e60 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b11e59
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e59
              | exact resolve b11e59 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e59
            have b11e64 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y x) X0) := by
              intro X0
              first
              | (have i₁ := b11e33 X0 y
                 have i₂ := b11e42 x
                 grind)
              | exact superpose b11e42 b11e33
              | exact resolve b11e33 b11e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33
            have b11e67 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op X1 (M.op y X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e14 X1 X0 y X2
                 have i₂ := b11e42 X0
                 grind)
              | (have i₁ := b11e14 X0 y X0 x
                 have i₂ := b11e42 X0
                 grind)
              | exact superpose b11e42 b11e14
              | exact resolve b11e14 b11e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b11e20 X0 X1
                 have i₂ := b11e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b11e19 b11e20
              | (have j1 := b11e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b11e20 b11e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e80 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b11e14 X1 X2 X3 X2
                 have i₂ := b11e19 X2 X0
                 grind)
              | (have i₁ := b11e14 X0 X1 X2 X3
                 have i₂ := b11e19 X0 (M.op X1 X3)
                 grind)
              | exact superpose b11e19 b11e14
              | (have j1 := b11e19 X2 X0
                 grind)
              | exact resolve b11e14 b11e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e83 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op (M.op X1 X2) (M.op X1 X3)) = X0 ∨ (M.op X0 (M.op X1 X2)) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b11e14 (M.op X1 X2) X1 X3 X2
                 have i₂ := b11e19 (M.op X1 X2) X0
                 grind)
              | (have i₁ := b11e14 X0 X1 X2 X3
                 have i₂ := b11e19 X0 (M.op (M.op X1 X3) X0)
                 grind)
              | exact superpose b11e19 b11e14
              | (have j1 := b11e19 (M.op X1 X2) X0
                 grind)
              | exact resolve b11e14 b11e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e97 : y = (k x y) ∨ y = (M.op y x) := by grind
            have b11e99 : y = (k x y) := by
              first
              | (have r₁ := b11e97
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e97 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e97
            have b11e250 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ x)
                 have i₂ := b11e60
                 grind)
              | exact superpose b11e60 b11e17
              | exact resolve b11e17 b11e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e255 : (σ x) ≠ (σ y) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b11e250
                 have i₂ := b11e99
                 grind)
              | exact superpose b11e99 b11e250
              | exact resolve b11e250 b11e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e250
            have b11e259 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b11e255
                 have i₂ := b11e20 x x
                 grind)
              | exact superpose b11e20 b11e255
              | exact resolve b11e255 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e255
            have b11e261 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
              first
              | (have i₁ := b11e259
                 have i₂ := b11e99
                 grind)
              | exact superpose b11e99 b11e259
              | exact resolve b11e259 b11e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e259
            have b11e273 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op y X1)) := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X0 y X1 x
                 have i₂ := b11e64 X0
                 grind)
              | exact superpose b11e64 b11e14
              | exact resolve b11e14 b11e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e64
            have b11e300 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b11e32 X0 (σ x)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e32
              | exact resolve b11e32 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e304 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op y (σ y)) X0) := by
              intro X0
              first
              | (have i₁ := b11e32 X0 y
                 have i₂ := b11e42 (σ y)
                 grind)
              | exact superpose b11e42 b11e32
              | exact resolve b11e32 b11e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e334 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b11e304 X0
                 have i₂ := b11e67 y X0 (σ y)
                 grind)
              | exact superpose b11e67 b11e304
              | exact resolve b11e304 b11e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e67 b11e304
            have b11e345 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b11e334 X0
                 have i₂ := b11e273 X0 y
                 grind)
              | exact superpose b11e273 b11e334
              | exact resolve b11e334 b11e273
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e273 b11e334
            have b11e370 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
              first
              | (have i₁ := b11e21
                 have i₂ := b11e345 (σ x)
                 grind)
              | exact superpose b11e345 b11e21
              | exact resolve b11e21 b11e345
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e394 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
              first
              | (have i₁ := b11e370
                 have i₂ := b11e42 (σ x)
                 grind)
              | exact superpose b11e42 b11e370
              | exact resolve b11e370 b11e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e370
            have b11e408 : (M.op y (σ x)) ≠ (σ (M.op y x)) := by
              first
              | (have i₁ := b11e394
                 have i₂ := b11e42 x
                 grind)
              | exact superpose b11e42 b11e394
              | exact resolve b11e394 b11e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e394
            have b11e579 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b11e345 X0
                 have i₂ := b11e300 X0
                 grind)
              | (have i₁ := b11e345 (σ y)
                 have i₂ := b11e300 (σ y)
                 grind)
              | exact superpose b11e300 b11e345
              | exact resolve b11e345 b11e300
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e584 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e14 X1 X0 X2 (σ y)
                 have i₂ := b11e300 X0
                 grind)
              | (have i₁ := b11e14 X0 (σ y) X2 X0
                 have i₂ := b11e300 X0
                 grind)
              | exact superpose b11e300 b11e14
              | exact resolve b11e14 b11e300
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e300
            have b11e605 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e584 X0 X1 X2
                 have i₂ := b11e32 X1 X0
                 grind)
              | exact superpose b11e32 b11e584
              | exact resolve b11e584 b11e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e32 b11e584
            have b11e616 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e605 X0 X1 X2
                 have i₂ := b11e345 X1
                 grind)
              | exact superpose b11e345 b11e605
              | exact resolve b11e605 b11e345
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e605
            have b11e650 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (σ y) x)) := by
              intro X0
              first
              | (have i₁ := b11e39 X0 (M.op (σ y) x)
                 have i₂ := b11e38 x x
                 grind)
              | exact superpose b11e38 b11e39
              | exact resolve b11e39 b11e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e39
            have b11e673 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b11e650 X0
                 have i₂ := b11e38 X0 x
                 grind)
              | exact superpose b11e38 b11e650
              | exact resolve b11e650 b11e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e650
            have b11e1025 : (σ y) = (M.op y (σ x)) := by
              first
              | (have i₁ := b11e24
                 have i₂ := b11e673 (σ x)
                 grind)
              | exact superpose b11e673 b11e24
              | exact resolve b11e24 b11e673
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e673
            have b11e6576 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b11e19 X0 X3
                 have i₂ := b11e80 X0 X0 X1 X2
                 grind)
              | (have i₁ := b11e19 (M.op X2 X3) X1
                 have i₂ := b11e80 X0 (M.op X2 X3) X2 X3
                 grind)
              | exact superpose b11e80 b11e19
              | (have j0 := b11e19 X0 X3
                 have j1 := b11e80 X3 X1 X0 X3
                 grind)
              | exact resolve b11e19 b11e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e6714 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X2
              first
              | (have j0 := b11e80 X0 X1 X1 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e80
            have b11e6717 : ∀ X0 X1 : G, (M.op X1 y) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b11e6714 X0 X1 x
                 have i₂ := b11e616 X1 X1 x
                 grind)
              | exact superpose b11e616 b11e6714
              | (have j0 := b11e6714 X0 X1 x
                 grind)
              | (have r₁ := b11e6714 (M.op X0 y) X0 x
                 have r₂ := b11e616 X0 X0 x
                 grind)
              | exact resolve b11e6714 b11e616
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e6714
            have b11e6830 : ∀ X0 X1 X3 : G, (M.op X0 y) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X3
              first
              | (have i₁ := b11e6576 X0 X1 x X3
                 have i₂ := b11e616 X1 X0 x
                 grind)
              | exact superpose b11e616 b11e6576
              | (have j0 := b11e6576 X0 X1 x X3
                 grind)
              | exact resolve b11e6576 b11e616
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e616 b11e6576
            have b11e6986 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X3
              first
              | (have j0 := b11e6830 X0 X1 X3
                 have j1 := b11e6717 X0 X1
                 grind)
              | (have r₁ := b11e6830 X1 X1 X0
                 have r₂ := b11e6717 X0 X1
                 grind)
              | (have r₁ := b11e6830 X0 X1 (M.op X1 y)
                 have r₂ := b11e6717 (M.op X0 y) X1
                 grind)
              | (have r₁ := b11e6830 X1 X1 y
                 have r₂ := b11e6717 (k X1 y) X1
                 grind)
              | exact resolve b11e6830 b11e6717
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e6830
            have b11e8491 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b11e78 x x
                 have i₂ := b11e60
                 grind)
              | exact superpose b11e60 b11e78
              | exact resolve b11e78 b11e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e60 b11e78
            have b11e8633 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by grind
            clear b11e8491
            have b11e8743 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k x x)) := by
              first
              | (have i₁ := b11e8633
                 have i₂ := b11e99
                 grind)
              | exact superpose b11e99 b11e8633
              | exact resolve b11e8633 b11e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e8633
            have b11e8838 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b11e8743
                 have i₂ := b11e99
                 grind)
              | exact superpose b11e99 b11e8743
              | exact resolve b11e8743 b11e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e8743
            have b11e8903 : (σ y) = (σ (k x x)) := by
              first
              | (have r₁ := b11e8838
                 have r₂ := b11e261
                 grind)
              | exact resolve b11e8838 b11e261
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e261 b11e8838
            have b11e9068 : (k x x) = (τ (σ y)) := by
              first
              | (have i₁ := b11e15 (k x x)
                 have i₂ := b11e8903
                 grind)
              | exact superpose b11e8903 b11e15
              | exact resolve b11e15 b11e8903
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e9069 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (σ y) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b11e20 (k x x) X0
                 have i₂ := b11e8903
                 grind)
              | exact superpose b11e8903 b11e20
              | exact resolve b11e20 b11e8903
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e8903
            have b11e9083 : ∀ X0 : G, (σ (k y X0)) = (σ (k (k x x) X0)) := by
              intro X0
              first
              | (have i₁ := b11e9069 X0
                 have i₂ := b11e20 y X0
                 grind)
              | exact superpose b11e20 b11e9069
              | exact resolve b11e9069 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e9069
            have b11e9084 : y = (k x x) := by
              first
              | (have i₁ := b11e9068
                 have i₂ := b11e15 y
                 grind)
              | exact superpose b11e15 b11e9068
              | exact resolve b11e9068 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e9068
            have b11e9263 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b11e83 X0 (σ y) (σ x) x
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e83
              | exact resolve b11e83 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e83
            have b11e9578 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) y) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b11e9263 X0 X1
                 have i₂ := b11e579 (M.op (σ y) X0)
                 grind)
              | exact superpose b11e579 b11e9263
              | (have j0 := b11e9263 X0 X1
                 grind)
              | exact resolve b11e9263 b11e579
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e9263
            have b11e9783 : ∀ X0 X1 : G, (M.op y (M.op (σ y) X0)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b11e9578 X0 X1
                 have i₂ := b11e42 (M.op (σ y) X0)
                 grind)
              | exact superpose b11e42 b11e9578
              | (have j0 := b11e9578 X0 X1
                 grind)
              | exact resolve b11e9578 b11e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e9578
            have b11e9981 : ∀ X1 : G, (M.op (σ y) y) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X1
              first
              | (have i₁ := b11e9783 x X1
                 have i₂ := b11e38 y x
                 grind)
              | exact superpose b11e38 b11e9783
              | (have j0 := b11e9783 x X1
                 grind)
              | exact resolve b11e9783 b11e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e38 b11e9783
            have b11e10154 : ∀ X1 : G, (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X1
              first
              | (have j0 := b11e9981 X1
                 have j1 := b11e6717 X1 (σ y)
                 grind)
              | (have r₁ := b11e9981 x
                 have r₂ := b11e6717 x (σ y)
                 grind)
              | (have r₁ := b11e9981 (M.op X1 y)
                 have r₂ := b11e6717 (M.op (σ y) y) X1
                 grind)
              | (have r₁ := b11e9981 y
                 have r₂ := b11e6717 (k (σ y) y) (σ y)
                 grind)
              | exact resolve b11e9981 b11e6717
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e6717 b11e9981
            have b11e10298 : ∀ X1 : G, (M.op X1 y) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X1
              first
              | (have i₁ := b11e10154 X1
                 have i₂ := b11e579 X1
                 grind)
              | exact superpose b11e579 b11e10154
              | (have j0 := b11e10154 X1
                 grind)
              | exact resolve b11e10154 b11e579
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e579 b11e10154
            have b11e10396 : ∀ X1 : G, (M.op X1 y) = (k (σ y) X1) ∨ (M.op X1 y) = X1 := by
              intro X1
              first
              | (have i₁ := b11e10298 X1
                 have i₂ := b11e345 X1
                 grind)
              | exact superpose b11e345 b11e10298
              | (have j0 := b11e10298 X1
                 grind)
              | exact resolve b11e10298 b11e345
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e345 b11e10298
            have b11e24650 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) y) := by
              intro X0
              first
              | (have i₁ := b11e20 y X0
                 have i₂ := b11e10396 (σ X0)
                 grind)
              | exact superpose b11e10396 b11e20
              | (have j1 := b11e10396 (σ X0)
                 grind)
              | exact resolve b11e20 b11e10396
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e10396
            have b11e24671 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) ∨ (σ X0) = (M.op (σ X0) y) := by
              intro X0
              first
              | (have i₁ := b11e24650 X0
                 have i₂ := b11e42 (σ X0)
                 grind)
              | exact superpose b11e42 b11e24650
              | (have j0 := b11e24650 X0
                 grind)
              | exact resolve b11e24650 b11e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e24650
            have b11e24677 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) ∨ (σ X0) = (M.op y (σ X0)) := by
              intro X0
              first
              | (have i₁ := b11e24671 X0
                 have i₂ := b11e42 (σ X0)
                 grind)
              | exact superpose b11e42 b11e24671
              | (have j0 := b11e24671 X0
                 grind)
              | exact resolve b11e24671 b11e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e24671
            have b11e50639 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (k X0 x) ∨ y = (M.op y x) ∨ x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b11e99
                 have i₂ := b11e6986 x X0 y
                 grind)
              | exact superpose b11e6986 b11e99
              | (have j1 := b11e6986 x X0 y
                 grind)
              | exact resolve b11e99 b11e6986
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e99 b11e6986
            have b11e50673 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (k X0 x) ∨ x = (M.op x X0) := by
              intro X0
              first
              | (have j0 := b11e50639 X0
                 grind)
              | (have r₁ := b11e50639 X0
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e50639 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e50639
            have b11e50802 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 x) = (k X0 x) ∨ x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b11e50673 X0
                 have i₂ := b11e42 x
                 grind)
              | exact superpose b11e42 b11e50673
              | (have j0 := b11e50673 X0
                 grind)
              | exact resolve b11e50673 b11e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e42 b11e50673
            have b11e50877 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ x = (M.op x X0) := by
              intro X0
              first
              | (have j0 := b11e50802 X0
                 grind)
              | (have r₁ := b11e50802 X0
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e50802 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e50802
            have b11e123479 : (σ (k y x)) = (σ (M.op (k x x) x)) ∨ x = (M.op x (k x x)) := by
              first
              | (have i₁ := b11e9083 x
                 have i₂ := b11e50877 (k x x)
                 grind)
              | exact superpose b11e50877 b11e9083
              | (have j1 := b11e50877 (k x x)
                 grind)
              | exact resolve b11e9083 b11e50877
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e9083 b11e50877
            have b11e123485 : (σ (M.op y x)) = (σ (k y x)) ∨ x = (M.op x (k x x)) := by
              first
              | (have i₁ := b11e123479
                 have i₂ := b11e9084
                 grind)
              | exact superpose b11e9084 b11e123479
              | exact resolve b11e123479 b11e9084
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e123479
            have b11e123493 : x = (M.op x y) ∨ (σ (M.op y x)) = (σ (k y x)) := by
              first
              | (have i₁ := b11e123485
                 have i₂ := b11e9084
                 grind)
              | exact superpose b11e9084 b11e123485
              | exact resolve b11e123485 b11e9084
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e9084 b11e123485
            have b11e123498 : (σ (M.op y x)) = (σ (k y x)) := by
              first
              | (have r₁ := b11e123493
                 have r₂ := b11e25
                 grind)
              | exact resolve b11e123493 b11e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e123493
            have b11e169257 : (M.op y (σ x)) = (σ (M.op y x)) ∨ (σ x) = (M.op y (σ x)) := by
              first
              | (have i₁ := b11e123498
                 have i₂ := b11e24677 x
                 grind)
              | exact superpose b11e24677 b11e123498
              | (have j1 := b11e24677 x
                 grind)
              | exact resolve b11e123498 b11e24677
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e24677 b11e123498
            have b11e169291 : (σ x) = (M.op y (σ x)) := by
              first
              | (have r₁ := b11e169257
                 have r₂ := b11e408
                 grind)
              | exact resolve b11e169257 b11e408
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e408 b11e169257
            have b11e169320 : (σ x) = (σ y) := by
              first
              | (have i₁ := b11e169291
                 have i₂ := b11e1025
                 grind)
              | exact superpose b11e1025 b11e169291
              | exact resolve b11e169291 b11e1025
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1025 b11e169291
            have b11e169360 : x = (τ (σ y)) := by
              first
              | (have i₁ := b11e15 x
                 have i₂ := b11e169320
                 grind)
              | exact superpose b11e169320 b11e15
              | exact resolve b11e15 b11e169320
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e169320
            have b11e169518 : x = y := by
              first
              | (have i₁ := b11e169360
                 have i₂ := b11e15 y
                 grind)
              | exact superpose b11e15 b11e169360
              | exact resolve b11e169360 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e169360
            have b11e169983 : y ≠ (M.op y y) := by
              first
              | (have i₁ := b11e22
                 have i₂ := b11e169518
                 grind)
              | exact superpose b11e169518 b11e22
              | exact resolve b11e22 b11e169518
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e169984 : y = (M.op y y) := by
              first
              | (have i₁ := b11e23
                 have i₂ := b11e169518
                 grind)
              | exact superpose b11e169518 b11e23
              | exact resolve b11e23 b11e169518
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e169518
            have b11e170069 : False := by grind
            exact b11e170069
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b12e22 : y ≠ (M.op y x) := by grind
            have b12e23 : y = (M.op x x) := by grind
            have b12e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e41 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y X0) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X0 x X1 x
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e14
              | exact resolve b12e14 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e42 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op x X0) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X0 x X1 y
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e45 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b12e41 X0 x
                 have i₂ := b12e42 X0 x
                 grind)
              | exact superpose b12e42 b12e41
              | exact resolve b12e41 b12e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e41 b12e42
            have b12e51 : y ≠ (M.op x x) := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e45 x
                 grind)
              | exact superpose b12e45 b12e22
              | exact resolve b12e22 b12e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e45
            have b12e52 : False := by grind
            exact b12e52
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b13e23 : y ≠ (M.op y x) := by grind
              have b13e24 : y = (M.op x x) := by grind
              have b13e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e39 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X0 x x X1
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e40 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 x) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X0 y y X1
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e15
                | exact resolve b13e15 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e46 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y X0) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X0 x X1 x
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e50 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b13e39 X0 x
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e39
                | exact resolve b13e39 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e79 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b13e23
                   have i₂ := b13e50 x
                   grind)
                | exact superpose b13e50 b13e23
                | exact resolve b13e23 b13e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e50
              have b13e213 : ∀ X1 : G, (M.op X1 y) = (M.op (M.op y x) X1) := by
                intro X1
                first
                | (have i₁ := b13e39 X1 (M.op x x)
                   have i₂ := b13e46 x x
                   grind)
                | exact superpose b13e46 b13e39
                | exact resolve b13e39 b13e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e39 b13e46
              have b13e230 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b13e213 X1
                   have i₂ := b13e40 X1 x
                   grind)
                | exact superpose b13e40 b13e213
                | exact resolve b13e213 b13e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e40 b13e213
              have b13e352 : y ≠ (M.op x x) := by
                first
                | (have i₁ := b13e79
                   have i₂ := b13e230 x
                   grind)
                | exact superpose b13e230 b13e79
                | exact resolve b13e79 b13e230
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e79 b13e230
              have b13e373 : False := by grind
              exact b13e373
            · have b14e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e23 : y ≠ (M.op y x) := by grind
              have b14e24 : y = (M.op x x) := by grind
              have b14e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b14e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              have b14e27 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e38 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op X0 (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 (σ x) (σ x) X1
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e15
                | exact resolve b14e15 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e39 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 x x X1
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e40 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
                intro X0 X1 X2 X4
                first
                | (have i₁ := b14e15 X2 X0 x X4
                   have i₂ := b14e15 X2 X0 x X1
                   grind)
                | (have i₁ := b14e15 (M.op X1 x) X1 X2 x
                   have i₂ := b14e15 (M.op X1 X2) X1 X2 x
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e44 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op (σ y) X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 (σ x) X1 (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e15
                | exact resolve b14e15 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e45 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 x X1 x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e48 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b14e39 X0 x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e39
                | exact resolve b14e39 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e39
              have b14e63 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b14e18 (σ x) (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e18
                | exact resolve b14e18 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e65 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
                first
                | (have i₁ := b14e63
                   have i₂ := b14e21 x x
                   grind)
                | exact superpose b14e21 b14e63
                | exact resolve b14e63 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e63
              have b14e70 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op X1 (M.op y X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X1 X0 y X2
                   have i₂ := b14e48 X0
                   grind)
                | (have i₁ := b14e15 X0 y X0 x
                   have i₂ := b14e48 X0
                   grind)
                | exact superpose b14e48 b14e15
                | exact resolve b14e15 b14e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e76 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b14e23
                   have i₂ := b14e48 x
                   grind)
                | exact superpose b14e48 b14e23
                | exact resolve b14e23 b14e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X0 X1
                   have i₂ := b14e20 (σ X0) (σ X1)
                   grind)
                | exact superpose b14e20 b14e21
                | (have j1 := b14e20 (σ X0) (σ X1)
                   grind)
                | exact resolve b14e21 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e86 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X1 X2 X3 X2
                   have i₂ := b14e20 X2 X0
                   grind)
                | (have i₁ := b14e15 X0 X1 X2 X3
                   have i₂ := b14e20 X0 (M.op X1 X3)
                   grind)
                | exact superpose b14e20 b14e15
                | (have j1 := b14e20 X2 X0
                   grind)
                | exact resolve b14e15 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e89 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op (M.op X1 X2) (M.op X1 X3)) = X0 ∨ (M.op X0 (M.op X1 X2)) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 (M.op X1 X2) X1 X3 X2
                   have i₂ := b14e20 (M.op X1 X2) X0
                   grind)
                | (have i₁ := b14e15 X0 X1 X2 X3
                   have i₂ := b14e20 X0 (M.op (M.op X1 X3) X0)
                   grind)
                | exact superpose b14e20 b14e15
                | (have j1 := b14e20 (M.op X1 X2) X0
                   grind)
                | exact resolve b14e15 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e105 : y = (k x y) ∨ y = (M.op y x) := by grind
              have b14e109 : y = (k x y) := by
                first
                | (have r₁ := b14e105
                   have r₂ := b14e23
                   grind)
                | exact resolve b14e105 b14e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e105
              have b14e215 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b14e38 X0 (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e38
                | exact resolve b14e38 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e219 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op y (σ x)) X0) := by
                intro X0
                first
                | (have i₁ := b14e38 X0 y
                   have i₂ := b14e48 (σ x)
                   grind)
                | exact superpose b14e48 b14e38
                | exact resolve b14e38 b14e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e38
              have b14e249 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op y y)) := by
                intro X0
                first
                | (have i₁ := b14e219 X0
                   have i₂ := b14e70 y X0 (σ x)
                   grind)
                | exact superpose b14e70 b14e219
                | exact resolve b14e219 b14e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e219
              have b14e333 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b14e40 X2 X3 X4 (M.op X0 x)
                   have i₂ := b14e15 X2 X0 x X1
                   grind)
                | (have i₁ := b14e40 (M.op X1 X3) X1 X2 X0
                   have i₂ := b14e15 X0 X1 X2 X3
                   grind)
                | exact superpose b14e15 b14e40
                | exact resolve b14e40 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e336 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e40 X0 X1 X2 y
                   have i₂ := b14e48 X0
                   grind)
                | (have i₁ := b14e40 y X1 X2 X0
                   have i₂ := b14e48 X0
                   grind)
                | exact superpose b14e48 b14e40
                | exact resolve b14e40 b14e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e40
              have b14e396 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y (M.op X0 X1)) X4) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b14e333 X0 X1 X2 X3 X4
                   have i₂ := b14e336 (M.op X0 X1) X2 X4
                   grind)
                | exact superpose b14e336 b14e333
                | exact resolve b14e333 b14e336
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e333
              have b14e410 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op X4 (M.op y y)) := by
                intro X2 X3 X4
                first
                | (have i₁ := b14e396 x x X2 X3 X4
                   have i₂ := b14e70 y X4 (M.op x x)
                   grind)
                | exact superpose b14e70 b14e396
                | exact resolve b14e396 b14e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e396
              have b14e416 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op X4 (σ y)) := by
                intro X2 X3 X4
                first
                | (have i₁ := b14e410 X2 X3 X4
                   have i₂ := b14e249 X4
                   grind)
                | exact superpose b14e249 b14e410
                | exact resolve b14e410 b14e249
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e410
              have b14e429 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op (σ y) X0) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X1 X0 X2 (σ y)
                   have i₂ := b14e215 X0
                   grind)
                | (have i₁ := b14e15 X0 (σ y) X2 X0
                   have i₂ := b14e215 X0
                   grind)
                | exact superpose b14e215 b14e15
                | exact resolve b14e15 b14e215
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e430 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op X1 (M.op (σ y) X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X1 X0 (σ y) X2
                   have i₂ := b14e215 X0
                   grind)
                | (have i₁ := b14e15 X0 (σ y) X0 x
                   have i₂ := b14e215 X0
                   grind)
                | exact superpose b14e215 b14e15
                | exact resolve b14e15 b14e215
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e442 : (σ y) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e25
                   have i₂ := b14e215 (σ x)
                   grind)
                | exact superpose b14e215 b14e25
                | exact resolve b14e25 b14e215
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e447 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (M.op (σ y) X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e430 X0 X1 x
                   have i₂ := b14e416 X0 x X1
                   grind)
                | (have i₁ := b14e430 X0 (σ y) x
                   have i₂ := b14e416 x x (M.op X0 x)
                   grind)
                | exact superpose b14e416 b14e430
                | exact resolve b14e430 b14e416
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e416 b14e430
              have b14e448 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op y (σ y)) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e429 X0 X1 X2
                   have i₂ := b14e336 (σ y) X0 X1
                   grind)
                | exact superpose b14e336 b14e429
                | exact resolve b14e429 b14e336
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e336 b14e429
              have b14e454 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op y y)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e448 X0 X1 X2
                   have i₂ := b14e70 y X1 (σ y)
                   grind)
                | exact superpose b14e70 b14e448
                | exact resolve b14e448 b14e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e70 b14e448
              have b14e460 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X0 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e454 X0 X1 X2
                   have i₂ := b14e249 X1
                   grind)
                | exact superpose b14e249 b14e454
                | exact resolve b14e454 b14e249
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e249 b14e454
              have b14e485 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (σ y) x)) := by
                intro X0
                first
                | (have i₁ := b14e45 X0 (M.op (σ x) x)
                   have i₂ := b14e44 x x
                   grind)
                | exact superpose b14e44 b14e45
                | exact resolve b14e45 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e45
              have b14e509 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b14e485 X0
                   have i₂ := b14e447 x X0
                   grind)
                | exact superpose b14e447 b14e485
                | exact resolve b14e485 b14e447
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e447 b14e485
              have b14e586 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e509 (σ x)
                   grind)
                | exact superpose b14e509 b14e22
                | exact resolve b14e22 b14e509
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e587 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b14e215 X0
                   have i₂ := b14e509 X0
                   grind)
                | exact superpose b14e509 b14e215
                | exact resolve b14e215 b14e509
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e907 : (σ y) ≠ (M.op y (σ x)) := by
                first
                | (have i₁ := b14e442
                   have i₂ := b14e509 (σ x)
                   grind)
                | exact superpose b14e509 b14e442
                | exact resolve b14e442 b14e509
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e442
              have b14e7370 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e20 X0 X3
                   have i₂ := b14e86 X0 X0 X1 X2
                   grind)
                | (have i₁ := b14e20 (M.op X2 X3) X1
                   have i₂ := b14e86 X0 (M.op X2 X3) X2 X3
                   grind)
                | exact superpose b14e86 b14e20
                | (have j0 := b14e20 X0 X3
                   have j1 := b14e86 X3 X1 X0 X3
                   grind)
                | exact resolve b14e20 b14e86
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e7505 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1 X2
                first
                | (have j0 := b14e86 X0 X1 X1 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e86
              have b14e7508 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e7505 X0 X1 x
                   have i₂ := b14e460 X1 X1 x
                   grind)
                | exact superpose b14e460 b14e7505
                | (have j0 := b14e7505 X0 X1 x
                   grind)
                | (have r₁ := b14e7505 (M.op X0 (σ y)) X0 x
                   have r₂ := b14e460 X0 X0 x
                   grind)
                | exact resolve b14e7505 b14e460
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7505
              have b14e7620 : ∀ X0 X1 X3 : G, (M.op X0 (σ y)) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1 X3
                first
                | (have i₁ := b14e7370 X0 X1 x X3
                   have i₂ := b14e460 X1 X0 x
                   grind)
                | exact superpose b14e460 b14e7370
                | (have j0 := b14e7370 X0 X1 x X3
                   grind)
                | exact resolve b14e7370 b14e460
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7370
              have b14e7704 : ∀ X0 X1 : G, (M.op y X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e7508 X0 X1
                   have i₂ := b14e509 X1
                   grind)
                | exact superpose b14e509 b14e7508
                | (have j0 := b14e7508 X0 X1
                   grind)
                | (have r₁ := b14e7508 (M.op y X0) X0
                   have r₂ := b14e509 X0
                   grind)
                | (have r₁ := b14e7508 (M.op (σ y) (σ y)) y
                   have r₂ := b14e509 (σ y)
                   grind)
                | exact resolve b14e7508 b14e509
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7508
              have b14e7782 : ∀ X0 X1 X3 : G, (M.op y X0) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1 X3
                first
                | (have i₁ := b14e7620 X0 X1 X3
                   have i₂ := b14e509 X0
                   grind)
                | exact superpose b14e509 b14e7620
                | (have j0 := b14e7620 X0 X1 X3
                   grind)
                | exact resolve b14e7620 b14e509
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7620
              have b14e7899 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1 X3
                first
                | (have j0 := b14e7782 X0 X1 X3
                   have j1 := b14e7704 X0 X1
                   grind)
                | (have r₁ := b14e7782 X1 X1 X0
                   have r₂ := b14e7704 X0 X1
                   grind)
                | (have r₁ := b14e7782 X0 X1 (M.op y X1)
                   have r₂ := b14e7704 (M.op y X0) X1
                   grind)
                | (have r₁ := b14e7782 y X1 X1
                   have r₂ := b14e7704 (k y X1) X1
                   grind)
                | exact resolve b14e7782 b14e7704
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7782
              have b14e9872 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b14e83 x x
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e83
                | exact resolve b14e83 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e83
              have b14e10017 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
              clear b14e9872
              have b14e10133 : (σ y) = (σ (k x x)) := by
                first
                | (have r₁ := b14e10017
                   have r₂ := b14e65
                   grind)
                | exact resolve b14e10017 b14e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e65 b14e10017
              have b14e10476 : (k x x) = (τ (σ y)) := by
                first
                | (have i₁ := b14e16 (k x x)
                   have i₂ := b14e10133
                   grind)
                | exact superpose b14e10133 b14e16
                | exact resolve b14e16 b14e10133
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e10477 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (σ y) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b14e21 (k x x) X0
                   have i₂ := b14e10133
                   grind)
                | exact superpose b14e10133 b14e21
                | exact resolve b14e21 b14e10133
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e10133
              have b14e10495 : ∀ X0 : G, (σ (k y X0)) = (σ (k (k x x) X0)) := by
                intro X0
                first
                | (have i₁ := b14e10477 X0
                   have i₂ := b14e21 y X0
                   grind)
                | exact superpose b14e21 b14e10477
                | exact resolve b14e10477 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e10477
              have b14e10496 : y = (k x x) := by
                first
                | (have i₁ := b14e10476
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e10476
                | exact resolve b14e10476 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e10476
              have b14e10689 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) X0)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e89 X0 (σ x) (σ x) x
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e89
                | exact resolve b14e89 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e89
              have b14e10979 : ∀ X0 X1 : G, (M.op y (M.op (σ x) X0)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e10689 X0 X1
                   have i₂ := b14e587 (M.op (σ x) X0)
                   grind)
                | exact superpose b14e587 b14e10689
                | (have j0 := b14e10689 X0 X1
                   grind)
                | exact resolve b14e10689 b14e587
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e10689
              have b14e11169 : ∀ X1 : G, (M.op (σ y) y) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
                intro X1
                first
                | (have i₁ := b14e10979 x X1
                   have i₂ := b14e44 y x
                   grind)
                | exact superpose b14e44 b14e10979
                | (have j0 := b14e10979 x X1
                   grind)
                | exact resolve b14e10979 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e44 b14e10979
              have b14e11350 : ∀ X1 : G, (M.op y (σ y)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
                intro X1
                first
                | (have i₁ := b14e11169 X1
                   have i₂ := b14e215 y
                   grind)
                | exact superpose b14e215 b14e11169
                | (have j0 := b14e11169 X1
                   grind)
                | exact resolve b14e11169 b14e215
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e215 b14e11169
              have b14e11522 : ∀ X1 : G, (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
                intro X1
                first
                | (have j0 := b14e11350 X1
                   have j1 := b14e7704 X1 (σ y)
                   grind)
                | (have r₁ := b14e11350 x
                   have r₂ := b14e7704 x (σ y)
                   grind)
                | (have r₁ := b14e11350 (M.op y X1)
                   have r₂ := b14e7704 (M.op y (σ y)) X1
                   grind)
                | (have r₁ := b14e11350 y
                   have r₂ := b14e7704 y (σ y)
                   grind)
                | exact resolve b14e11350 b14e7704
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7704 b14e11350
              have b14e11683 : ∀ X1 : G, (M.op y X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
                intro X1
                first
                | (have i₁ := b14e11522 X1
                   have i₂ := b14e587 X1
                   grind)
                | exact superpose b14e587 b14e11522
                | (have j0 := b14e11522 X1
                   grind)
                | exact resolve b14e11522 b14e587
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e587 b14e11522
              have b14e11842 : ∀ X1 : G, (M.op y X1) = (k (σ y) X1) ∨ (M.op y X1) = X1 := by
                intro X1
                first
                | (have i₁ := b14e11683 X1
                   have i₂ := b14e509 X1
                   grind)
                | exact superpose b14e509 b14e11683
                | (have j0 := b14e11683 X1
                   grind)
                | exact resolve b14e11683 b14e509
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e11683
              have b14e24139 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op y (σ X0)) := by
                intro X0
                first
                | (have i₁ := b14e21 y X0
                   have i₂ := b14e11842 (σ X0)
                   grind)
                | exact superpose b14e11842 b14e21
                | (have j1 := b14e11842 (σ X0)
                   grind)
                | exact resolve b14e21 b14e11842
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e11842
              have b14e67342 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (k X0 x) ∨ y = (M.op y x) ∨ x = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b14e109
                   have i₂ := b14e7899 x X0 y
                   grind)
                | exact superpose b14e7899 b14e109
                | (have j1 := b14e7899 x X0 y
                   grind)
                | exact resolve b14e109 b14e7899
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e109 b14e7899
              have b14e67365 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ y = (M.op y x) ∨ x = (M.op x X0) := by
                intro X0
                first
                | (have j0 := b14e67342 X0
                   grind)
                | (have r₁ := b14e67342 X0
                   have r₂ := b14e76
                   grind)
                | exact resolve b14e67342 b14e76
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e76 b14e67342
              have b14e67483 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ x = (M.op x X0) := by
                intro X0
                first
                | (have j0 := b14e67365 X0
                   grind)
                | (have r₁ := b14e67365 X0
                   have r₂ := b14e23
                   grind)
                | exact resolve b14e67365 b14e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e67365
              have b14e100864 : (σ (k y x)) = (σ (M.op (k x x) x)) ∨ x = (M.op x (k x x)) := by
                first
                | (have i₁ := b14e10495 x
                   have i₂ := b14e67483 (k x x)
                   grind)
                | exact superpose b14e67483 b14e10495
                | (have j1 := b14e67483 (k x x)
                   grind)
                | exact resolve b14e10495 b14e67483
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e10495 b14e67483
              have b14e100873 : (σ (k y x)) = (σ (M.op y x)) ∨ x = (M.op x (k x x)) := by
                first
                | (have i₁ := b14e100864
                   have i₂ := b14e10496
                   grind)
                | exact superpose b14e10496 b14e100864
                | exact resolve b14e100864 b14e10496
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e100864
              have b14e100879 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x (k x x)) := by
                first
                | (have i₁ := b14e100873
                   have i₂ := b14e48 x
                   grind)
                | exact superpose b14e48 b14e100873
                | exact resolve b14e100873 b14e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e48 b14e100873
              have b14e100885 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ (k y x)) := by
                first
                | (have i₁ := b14e100879
                   have i₂ := b14e10496
                   grind)
                | exact superpose b14e10496 b14e100879
                | exact resolve b14e100879 b14e10496
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e10496 b14e100879
              have b14e100889 : (σ (M.op x y)) = (σ (k y x)) := by
                first
                | (have r₁ := b14e100885
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e100885 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e100885
              have b14e201807 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (M.op y (σ x)) := by
                first
                | (have i₁ := b14e100889
                   have i₂ := b14e24139 x
                   grind)
                | exact superpose b14e24139 b14e100889
                | (have j1 := b14e24139 x
                   grind)
                | exact resolve b14e100889 b14e24139
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e24139 b14e100889
              have b14e201847 : (σ x) = (M.op y (σ x)) := by
                first
                | (have r₁ := b14e201807
                   have r₂ := b14e586
                   grind)
                | exact resolve b14e201807 b14e586
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e586 b14e201807
              have b14e201992 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b14e460 y X0 (σ x)
                   have i₂ := b14e201847
                   grind)
                | exact superpose b14e201847 b14e460
                | exact resolve b14e460 b14e201847
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e460 b14e201847
              have b14e202036 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b14e201992 X0
                   have i₂ := b14e509 X0
                   grind)
                | exact superpose b14e509 b14e201992
                | exact resolve b14e201992 b14e509
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e509 b14e201992
              have b14e203128 : (σ y) = (M.op y (σ x)) := by
                first
                | (have i₁ := b14e26
                   have i₂ := b14e202036 (σ x)
                   grind)
                | exact superpose b14e202036 b14e26
                | exact resolve b14e26 b14e202036
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e202036
              have b14e203571 : False := by grind
              exact b14e203571
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b15e22 : y ≠ (M.op y x) := by grind
            have b15e23 : y = (M.op x x) := by grind
            have b15e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e37 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X0 x X1 x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e38 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op x X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X0 x X1 y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e14
              | exact resolve b15e14 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e43 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b15e37 X0 x
                 have i₂ := b15e38 X0 x
                 grind)
              | exact superpose b15e38 b15e37
              | exact resolve b15e37 b15e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e37 b15e38
            have b15e49 : y ≠ (M.op x x) := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e43 x
                 grind)
              | exact superpose b15e43 b15e22
              | exact resolve b15e22 b15e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e43
            have b15e50 : False := by grind
            exact b15e50
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b16e23 : y ≠ (M.op y x) := by grind
              have b16e24 : y = (M.op x x) := by grind
              have b16e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e38 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X0 x x X1
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e39 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 x) := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X0 y y X1
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e15
                | exact resolve b16e15 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e44 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y X0) := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X0 x X1 x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e48 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b16e38 X0 x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e38
                | exact resolve b16e38 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e75 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b16e23
                   have i₂ := b16e48 x
                   grind)
                | exact superpose b16e48 b16e23
                | exact resolve b16e23 b16e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e48
              have b16e205 : ∀ X1 : G, (M.op X1 y) = (M.op (M.op y x) X1) := by
                intro X1
                first
                | (have i₁ := b16e38 X1 (M.op x x)
                   have i₂ := b16e44 x x
                   grind)
                | exact superpose b16e44 b16e38
                | exact resolve b16e38 b16e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e38 b16e44
              have b16e222 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b16e205 X1
                   have i₂ := b16e39 X1 x
                   grind)
                | exact superpose b16e39 b16e205
                | exact resolve b16e205 b16e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e39 b16e205
              have b16e344 : y ≠ (M.op x x) := by
                first
                | (have i₁ := b16e75
                   have i₂ := b16e222 x
                   grind)
                | exact superpose b16e222 b16e75
                | exact resolve b16e75 b16e222
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e75 b16e222
              have b16e365 : False := by grind
              exact b16e365
            · have b17e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : y ≠ (M.op y x) := by grind
              have b17e24 : y = (M.op x x) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e36 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X0 x x X1
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e37 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X3) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
                intro X0 X1 X2 X3 X5
                first
                | (have i₁ := b17e15 X3 X2 (M.op X0 x) X5
                   have i₂ := b17e15 X2 X0 x X1
                   grind)
                | (have i₁ := b17e15 X0 (M.op X1 X3) X0 X3
                   have i₂ := b17e15 X0 X1 X2 X3
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e39 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
                intro X0 X1 X2 X4
                first
                | (have i₁ := b17e15 X2 X0 x X4
                   have i₂ := b17e15 X2 X0 x X1
                   grind)
                | (have i₁ := b17e15 (M.op X1 x) X1 X2 x
                   have i₂ := b17e15 (M.op X1 X2) X1 X2 x
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e41 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X0 x X1 x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e44 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 X0 X1 X2 x
                   have i₂ := b17e15 X0 X1 X3 x
                   grind)
                | (have i₁ := b17e15 (M.op X1 X2) X1 X2 X3
                   have i₂ := b17e15 (M.op X1 X3) X1 X2 X3
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e46 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b17e36 X0 x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e36
                | exact resolve b17e36 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e36
              have b17e65 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op y X0) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X1 X0 X2 y
                   have i₂ := b17e46 X0
                   grind)
                | (have i₁ := b17e15 X0 y X2 X0
                   have i₂ := b17e46 X0
                   grind)
                | exact superpose b17e46 b17e15
                | exact resolve b17e15 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e66 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op X1 (M.op y X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X1 X0 y X2
                   have i₂ := b17e46 X0
                   grind)
                | (have i₁ := b17e15 X0 y X0 x
                   have i₂ := b17e46 X0
                   grind)
                | exact superpose b17e46 b17e15
                | exact resolve b17e15 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e86 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b17e26
                   have i₂ := b17e20 (σ x) X0
                   grind)
                | (have i₁ := b17e26
                   have i₂ := b17e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b17e20 b17e26
                | (have j1 := b17e20 (σ x) X0
                   grind)
                | (have r₁ := b17e26
                   have r₂ := b17e20 (σ x) (σ y)
                   grind)
                | exact resolve b17e26 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e99 : y = (k x y) ∨ y = (M.op y x) := by grind
              have b17e103 : y = (k x y) := by
                first
                | (have r₁ := b17e99
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e99 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e99
              have b17e129 : ∀ X0 X2 : G, (M.op y X0) = (M.op (M.op x X2) X0) := by
                intro X0 X2
                first
                | (have i₁ := b17e15 X0 x x X2
                   have i₂ := b17e41 X0 x
                   grind)
                | exact superpose b17e41 b17e15
                | exact resolve b17e15 b17e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e41
              have b17e230 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e39 X0 X1 X2 y
                   have i₂ := b17e46 X0
                   grind)
                | (have i₁ := b17e39 y X1 X2 X0
                   have i₂ := b17e46 X0
                   grind)
                | exact superpose b17e46 b17e39
                | exact resolve b17e39 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e39
              have b17e297 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) x) X2) = (M.op y X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e129 X2 (M.op X0 x)
                   have i₂ := b17e15 x X0 x X1
                   grind)
                | exact superpose b17e15 b17e129
                | exact resolve b17e129 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e129
              have b17e334 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (M.op y (M.op X0 X1)) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e297 X0 X1 X2
                   have i₂ := b17e230 (M.op X0 X1) x X2
                   grind)
                | exact superpose b17e230 b17e297
                | exact resolve b17e297 b17e230
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e230 b17e297
              have b17e338 : ∀ X2 : G, (M.op y X2) = (M.op X2 (M.op y y)) := by
                intro X2
                first
                | (have i₁ := b17e334 x x X2
                   have i₂ := b17e66 y X2 (M.op x x)
                   grind)
                | exact superpose b17e66 b17e334
                | exact resolve b17e334 b17e66
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e66 b17e334
              have b17e374 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op y X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e44 X1 X0 X2 y
                   have i₂ := b17e46 X0
                   grind)
                | (have i₁ := b17e44 X0 y X2 X0
                   have i₂ := b17e46 X0
                   grind)
                | exact superpose b17e46 b17e44
                | exact resolve b17e44 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46
              have b17e475 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X0 y y X1
                   have i₂ := b17e338 X0
                   grind)
                | exact superpose b17e338 b17e15
                | exact resolve b17e15 b17e338
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e338
              have b17e608 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op (M.op X3 X4) X5)) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b17e44 X2 (M.op X3 X4) X0 X5
                   have i₂ := b17e37 X3 X4 X0 X2 X1
                   grind)
                | (have i₁ := b17e44 (M.op X2 X5) X1 X2 X3
                   have i₂ := b17e37 X0 X1 X2 (M.op X1 X2) X5
                   grind)
                | exact superpose b17e37 b17e44
                | exact resolve b17e44 b17e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e37 b17e44
              have b17e644 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op y (M.op X3 X4))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b17e608 X0 X1 X2 X3 X4 x
                   have i₂ := b17e374 (M.op X3 X4) X2 x
                   grind)
                | exact superpose b17e374 b17e608
                | exact resolve b17e608 b17e374
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e374 b17e608
              have b17e715 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y y) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e644 X0 X1 X2 x x
                   have i₂ := b17e65 y X2 (M.op x x)
                   grind)
                | exact superpose b17e65 b17e644
                | exact resolve b17e644 b17e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e65 b17e644
              have b17e774 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e715 X0 X1 X2
                   have i₂ := b17e475 X2 y
                   grind)
                | exact superpose b17e475 b17e715
                | exact resolve b17e715 b17e475
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e475 b17e715
              have b17e932 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op y X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X0 X1 X2 x
                   have i₂ := b17e774 X1 x X0
                   grind)
                | exact superpose b17e774 b17e15
                | exact resolve b17e15 b17e774
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e4533 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b17e86 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e86
              have b17e4534 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e4533
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e4533 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e4533
              have b17e4535 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e4534
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e4534
                | exact resolve b17e4534 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e4534
              have b17e4536 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b17e4535
                   have i₂ := b17e103
                   grind)
                | exact superpose b17e103 b17e4535
                | exact resolve b17e4535 b17e103
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e103 b17e4535
              have b17e4556 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b17e774 (σ x) (σ y) X0
                   have i₂ := b17e4536
                   grind)
                | exact superpose b17e4536 b17e774
                | exact resolve b17e774 b17e4536
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e774
              have b17e4558 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b17e932 X0 (σ x) (σ y)
                   have i₂ := b17e4536
                   grind)
                | exact superpose b17e4536 b17e932
                | exact resolve b17e932 b17e4536
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e932
              have b17e5003 : (σ y) ≠ (M.op y (σ x)) := by
                first
                | (have i₁ := b17e25
                   have i₂ := b17e4556 (σ x)
                   grind)
                | exact superpose b17e4556 b17e25
                | exact resolve b17e25 b17e4556
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e4556
              have b17e6457 : (σ y) = (M.op y (σ x)) := by
                first
                | (have i₁ := b17e4536
                   have i₂ := b17e4558 (σ x)
                   grind)
                | exact superpose b17e4558 b17e4536
                | exact resolve b17e4536 b17e4558
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e4536 b17e4558
              have b17e6545 : False := by grind
              exact b17e6545
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b18e21 : y ≠ (M.op y x) := by grind
          have b18e22 : y ≠ (M.op x x) := by grind
          have b18e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          have b18e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b18e20
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e20
            | exact resolve b18e20 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e35 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X0 (σ y) (σ x) X1
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e13
            | exact resolve b18e13 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e36 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X0 x y X1
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e42 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X0 x X1 y
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e45 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b18e36 X0 y
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e36
            | exact resolve b18e36 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e58 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X0 X0) = (k X0 (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e16 X0 (M.op X1 X3)
               have i₂ := b18e13 X0 X1 X2 X3
               grind)
            | (have i₁ := b18e16 (M.op X1 X2) X0
               have i₂ := b18e13 X0 X1 X2 X3
               grind)
            | exact superpose b18e13 b18e16
            | (have j0 := b18e16 X0 (M.op X1 X3)
               grind)
            | (have r₁ := b18e16 X0 (M.op X0 (M.op X0 X2))
               have r₂ := b18e13 X0 X0 X2 (M.op X0 X2)
               grind)
            | exact resolve b18e16 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e60 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
          have b18e63 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear b18e60
          have b18e64 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b18e63
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e63
            | exact resolve b18e63 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e63
          have b18e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e19 X0 X1
               have i₂ := b18e18 (σ X0) (σ X1)
               grind)
            | exact superpose b18e18 b18e19
            | (have j1 := b18e18 (σ X0) (σ X1)
               grind)
            | exact resolve b18e19 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e92 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X1 X0 X2 x
               have i₂ := b18e45 X0
               grind)
            | (have i₁ := b18e13 X0 x X2 X0
               have i₂ := b18e45 X0
               grind)
            | exact superpose b18e45 b18e13
            | exact resolve b18e13 b18e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e93 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x X0)) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X1 X0 x X2
               have i₂ := b18e45 X0
               grind)
            | (have i₁ := b18e13 X0 x X0 x
               have i₂ := b18e45 X0
               grind)
            | exact superpose b18e45 b18e13
            | exact resolve b18e13 b18e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e102 : ∀ X0 X1 X2 : G, (M.op x X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e93 X0 X1 X2
               have i₂ := b18e42 X1 X0
               grind)
            | exact superpose b18e42 b18e93
            | exact resolve b18e93 b18e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e42 b18e93
          have b18e103 : ∀ X0 X1 X2 : G, (M.op X1 x) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e92 X0 X1 X2
               have i₂ := b18e36 X1 X0
               grind)
            | exact superpose b18e36 b18e92
            | exact resolve b18e92 b18e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36 b18e92
          have b18e246 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b18e16 (σ x) (σ x)
               have i₂ := b18e64
               grind)
            | exact superpose b18e64 b18e16
            | exact resolve b18e16 b18e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e247 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op (σ (k x y)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X0 (σ x) X1 (σ x)
               have i₂ := b18e64
               grind)
            | exact superpose b18e64 b18e13
            | exact resolve b18e13 b18e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e248 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op X0 (σ (k x y))) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X0 (σ x) (σ x) X1
               have i₂ := b18e64
               grind)
            | exact superpose b18e64 b18e13
            | exact resolve b18e13 b18e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e249 : ∀ X0 : G, (M.op x X0) = (M.op X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b18e248 X0 x
               have i₂ := b18e102 (σ x) X0 x
               grind)
            | exact superpose b18e102 b18e248
            | exact resolve b18e248 b18e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e248
          have b18e250 : ∀ X0 : G, (M.op X0 x) = (M.op (σ (k x y)) X0) := by
            intro X0
            first
            | (have i₁ := b18e247 X0 x
               have i₂ := b18e103 (σ x) X0 x
               grind)
            | exact superpose b18e103 b18e247
            | exact resolve b18e247 b18e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e247
          have b18e251 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b18e246
               have i₂ := b18e19 x x
               grind)
            | exact superpose b18e19 b18e246
            | exact resolve b18e246 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e246
          have b18e302 : ∀ X0 X1 X3 : G, (M.op X3 (σ y)) = (M.op (M.op (M.op X0 X1) (σ y)) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e35 X3 (M.op X0 x)
               have i₂ := b18e13 (σ y) X0 x X1
               grind)
            | exact superpose b18e13 b18e35
            | exact resolve b18e35 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e35
          have b18e350 : ∀ X3 : G, (M.op x X3) = (M.op X3 (σ y)) := by
            intro X3
            first
            | (have i₁ := b18e302 x x X3
               have i₂ := b18e102 (M.op x x) X3 (σ y)
               grind)
            | exact superpose b18e102 b18e302
            | exact resolve b18e302 b18e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e102 b18e302
          have b18e389 : (σ x) ≠ (M.op x (σ x)) := by
            first
            | (have i₁ := b18e26
               have i₂ := b18e350 (σ x)
               grind)
            | exact superpose b18e350 b18e26
            | exact resolve b18e26 b18e350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e26 b18e350
          have b18e4698 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b18e58 X0 X0 x (M.op X0 X1)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e58
          have b18e4699 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b18e4698 X0 x
               have i₂ := b18e103 X0 X0 x
               grind)
            | exact superpose b18e103 b18e4698
            | exact resolve b18e4698 b18e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e103 b18e4698
          have b18e4880 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b18e4699 X0
               have i₂ := b18e45 X0
               grind)
            | (have i₁ := b18e4699 x
               have i₂ := b18e45 x
               grind)
            | exact superpose b18e45 b18e4699
            | exact resolve b18e4699 b18e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e45
          have b18e7222 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b18e71 x x
               have i₂ := b18e64
               grind)
            | exact superpose b18e64 b18e71
            | exact resolve b18e71 b18e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e71
          have b18e7364 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by grind
          clear b18e7222
          have b18e7468 : (σ (k x y)) = (σ (k x x)) := by
            first
            | (have r₁ := b18e7364
               have r₂ := b18e251
               grind)
            | exact resolve b18e7364 b18e251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e251 b18e7364
          have b18e7644 : (σ (M.op x y)) = (σ (k x x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b18e7468
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e7468
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e7468 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e7645 : (k x y) = (τ (σ (k x x))) := by
            first
            | (have i₁ := b18e14 (k x y)
               have i₂ := b18e7468
               grind)
            | exact superpose b18e7468 b18e14
            | exact resolve b18e14 b18e7468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e7657 : (k x y) = (k x x) := by
            first
            | (have i₁ := b18e7645
               have i₂ := b18e14 (k x x)
               grind)
            | exact superpose b18e14 b18e7645
            | exact resolve b18e7645 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e7645
          have b18e7658 : (σ (M.op x y)) = (σ (k x x)) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b18e7644
               have r₂ := b18e22
               grind)
            | exact resolve b18e7644 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e7644
          have b18e7660 : (σ (M.op x y)) = (σ (k x x)) := by
            first
            | (have r₁ := b18e7658
               have r₂ := b18e21
               grind)
            | exact resolve b18e7658 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e7658
          have b18e7662 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b18e7660
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e7660
            | exact resolve b18e7660 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e7660
          have b18e7715 : (M.op x y) = (k x x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b18e18 x y
               have i₂ := b18e7657
               grind)
            | exact superpose b18e7657 b18e18
            | (have j0 := b18e18 x y
               grind)
            | exact resolve b18e18 b18e7657
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e7657
          have b18e7716 : (M.op x y) = (k x x) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b18e7715
               have r₂ := b18e22
               grind)
            | exact resolve b18e7715 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e7715
          have b18e7724 : (M.op x y) = (k x x) := by
            first
            | (have r₁ := b18e7716
               have r₂ := b18e21
               grind)
            | exact resolve b18e7716 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e7716
          have b18e7732 : x = (k x x) := by
            first
            | (have i₁ := b18e7724
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e7724
            | exact resolve b18e7724 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e7724
          have b18e8894 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b18e18 x x
               have i₂ := b18e7732
               grind)
            | exact superpose b18e7732 b18e18
            | (have j0 := b18e18 x x
               grind)
            | exact resolve b18e18 b18e7732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e7732
          have b18e8895 : x = (M.op x x) := by grind
          clear b18e8894
          have b18e10402 : (M.op (σ (k x y)) (σ (k x y))) = (k (σ (k x y)) (M.op x x)) := by
            first
            | (have i₁ := b18e4880 (σ (k x y))
               have i₂ := b18e249 x
               grind)
            | exact superpose b18e249 b18e4880
            | exact resolve b18e4880 b18e249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e249 b18e4880
          have b18e10520 : (M.op (σ (k x y)) (σ (k x y))) = (k (σ (k x y)) x) := by
            first
            | (have i₁ := b18e10402
               have i₂ := b18e8895
               grind)
            | exact superpose b18e8895 b18e10402
            | exact resolve b18e10402 b18e8895
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e10402
          have b18e10563 : (M.op (σ (k x x)) (σ (k x x))) = (k (σ (k x x)) x) := by
            first
            | (have i₁ := b18e10520
               have i₂ := b18e7468
               grind)
            | exact superpose b18e7468 b18e10520
            | exact resolve b18e10520 b18e7468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e10520
          have b18e10586 : (M.op (σ x) (σ x)) = (k (σ x) x) := by
            first
            | (have i₁ := b18e10563
               have i₂ := b18e7662
               grind)
            | exact superpose b18e7662 b18e10563
            | exact resolve b18e10563 b18e7662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e10563
          have b18e10607 : (σ (k x y)) = (k (σ x) x) := by
            first
            | (have i₁ := b18e10586
               have i₂ := b18e64
               grind)
            | exact superpose b18e64 b18e10586
            | exact resolve b18e10586 b18e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e64 b18e10586
          have b18e10623 : (σ (k x x)) = (k (σ x) x) := by
            first
            | (have i₁ := b18e10607
               have i₂ := b18e7468
               grind)
            | exact superpose b18e7468 b18e10607
            | exact resolve b18e10607 b18e7468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e10607
          have b18e10634 : (σ x) = (k (σ x) x) := by
            first
            | (have i₁ := b18e10623
               have i₂ := b18e7662
               grind)
            | exact superpose b18e7662 b18e10623
            | exact resolve b18e10623 b18e7662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e10623
          have b18e10687 : ∀ X0 : G, (M.op X0 x) = (M.op (σ (k x x)) X0) := by
            intro X0
            first
            | (have i₁ := b18e250 X0
               have i₂ := b18e7468
               grind)
            | exact superpose b18e7468 b18e250
            | exact resolve b18e250 b18e7468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e10773 : (M.op (σ (k x y)) (σ (k x y))) = (k (σ (k x y)) (M.op x x)) := by
            first
            | (have i₁ := b18e4699 (σ (k x y))
               have i₂ := b18e250 x
               grind)
            | exact superpose b18e250 b18e4699
            | exact resolve b18e4699 b18e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e250 b18e4699
          have b18e10778 : (M.op (σ (k x y)) (σ (k x y))) = (k (σ (k x y)) x) := by
            first
            | (have i₁ := b18e10773
               have i₂ := b18e8895
               grind)
            | exact superpose b18e8895 b18e10773
            | exact resolve b18e10773 b18e8895
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e10773
          have b18e10852 : ∀ X0 : G, (M.op X0 x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b18e10687 X0
               have i₂ := b18e7662
               grind)
            | exact superpose b18e7662 b18e10687
            | exact resolve b18e10687 b18e7662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e10687
          have b18e10856 : (M.op (σ (k x x)) (σ (k x x))) = (k (σ (k x x)) x) := by
            first
            | (have i₁ := b18e10778
               have i₂ := b18e7468
               grind)
            | exact superpose b18e7468 b18e10778
            | exact resolve b18e10778 b18e7468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e7468 b18e10778
          have b18e10884 : (M.op (σ x) (σ x)) = (k (σ x) x) := by
            first
            | (have i₁ := b18e10856
               have i₂ := b18e7662
               grind)
            | exact superpose b18e7662 b18e10856
            | exact resolve b18e10856 b18e7662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e7662 b18e10856
          have b18e10907 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b18e10884
               have i₂ := b18e10634
               grind)
            | exact superpose b18e10634 b18e10884
            | exact resolve b18e10884 b18e10634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e10634 b18e10884
          have b18e10927 : (σ x) = (M.op (σ x) x) := by
            first
            | (have i₁ := b18e10907
               have i₂ := b18e10852 (σ x)
               grind)
            | exact superpose b18e10852 b18e10907
            | exact resolve b18e10907 b18e10852
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e10907
          have b18e10942 : (σ x) = (M.op x x) := by
            first
            | (have i₁ := b18e10927
               have i₂ := b18e10852 x
               grind)
            | exact superpose b18e10852 b18e10927
            | exact resolve b18e10927 b18e10852
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e10852 b18e10927
          have b18e10954 : x = (σ x) := by
            first
            | (have i₁ := b18e10942
               have i₂ := b18e8895
               grind)
            | exact superpose b18e8895 b18e10942
            | exact resolve b18e10942 b18e8895
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e10942
          have b18e10971 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b18e389
               have i₂ := b18e10954
               grind)
            | exact superpose b18e10954 b18e389
            | exact resolve b18e389 b18e10954
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e389 b18e10954
          have b18e10990 : False := by grind
          exact b18e10990
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op y x) := by grind
            have b19e23 : y ≠ (M.op x x) := by grind
            have b19e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b19e25 : x ≠ (M.op x y) := by grind
            have b19e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b19e20 X1 (τ X0)
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e20
              | exact resolve b19e20 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e30 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X3) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
              intro X0 X1 X2 X3 X5
              first
              | (have i₁ := b19e14 X3 X2 (M.op X0 x) X5
                 have i₂ := b19e14 X2 X0 x X1
                 grind)
              | (have i₁ := b19e14 X0 (M.op X1 X3) X0 X3
                 have i₂ := b19e14 X0 X1 X2 X3
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e32 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X0 (σ y) (σ x) X1
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e14
              | exact resolve b19e14 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e33 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 x) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X0 y y X1
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e14
              | exact resolve b19e14 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e34 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
              intro X0 X1 X2 X4
              first
              | (have i₁ := b19e14 X2 X0 x X4
                 have i₂ := b19e14 X2 X0 x X1
                 grind)
              | (have i₁ := b19e14 (M.op X1 x) X1 X2 x
                 have i₂ := b19e14 (M.op X1 X2) X1 X2 x
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e38 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ y) X0) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X0 (σ y) X1 (σ x)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e14
              | exact resolve b19e14 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e39 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op x X0) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X0 y X1 y
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e14
              | exact resolve b19e14 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e40 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e14 X0 X1 X2 x
                 have i₂ := b19e14 X0 X1 X3 x
                 grind)
              | (have i₁ := b19e14 (M.op X1 X2) X1 X2 X3
                 have i₂ := b19e14 (M.op X1 X3) X1 X2 X3
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e42 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b19e33 X0 y
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e33
              | exact resolve b19e33 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e48 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X0 y X1 x
                 have i₂ := b19e33 X0 x
                 grind)
              | exact superpose b19e33 b19e14
              | exact resolve b19e14 b19e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X0 X0) = (k X0 (M.op X1 X3)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e17 X0 (M.op X1 X3)
                 have i₂ := b19e14 X0 X1 X2 X3
                 grind)
              | (have i₁ := b19e17 (M.op X1 X2) X0
                 have i₂ := b19e14 X0 X1 X2 X3
                 grind)
              | exact superpose b19e14 b19e17
              | (have j0 := b19e17 X0 (M.op X1 X3)
                 grind)
              | (have r₁ := b19e17 X0 (M.op X0 (M.op X0 X2))
                 have r₂ := b19e14 X0 X0 X2 (M.op X0 X2)
                 grind)
              | exact resolve b19e17 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e57 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
            have b19e59 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear b19e57
            have b19e60 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b19e59
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e59
              | exact resolve b19e59 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e59
            have b19e68 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (M.op X0 X0) = (k X0 x) := by
              intro X0
              first
              | (have i₁ := b19e17 X0 x
                 have i₂ := b19e42 X0
                 grind)
              | (have i₁ := b19e17 x X0
                 have i₂ := b19e42 X0
                 grind)
              | exact superpose b19e42 b19e17
              | (have j0 := b19e17 X0 x
                 grind)
              | exact resolve b19e17 b19e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e71 : x ≠ (M.op y x) := by
              first
              | (have i₁ := b19e25
                 have i₂ := b19e42 y
                 grind)
              | exact superpose b19e42 b19e25
              | exact resolve b19e25 b19e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b19e20 X0 X1
                 have i₂ := b19e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b19e19 b19e20
              | (have j1 := b19e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b19e20 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e79 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e14 X1 X2 X3 X2
                 have i₂ := b19e19 X2 X0
                 grind)
              | (have i₁ := b19e14 X0 X1 X2 X3
                 have i₂ := b19e19 X0 (M.op X1 X3)
                 grind)
              | exact superpose b19e19 b19e14
              | (have j1 := b19e19 X2 X0
                 grind)
              | exact resolve b19e14 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e82 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op (M.op X1 X2) (M.op X1 X3)) = X0 ∨ (M.op X0 (M.op X1 X2)) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e14 (M.op X1 X2) X1 X3 X2
                 have i₂ := b19e19 (M.op X1 X2) X0
                 grind)
              | (have i₁ := b19e14 X0 X1 X2 X3
                 have i₂ := b19e19 X0 (M.op (M.op X1 X3) X0)
                 grind)
              | exact superpose b19e19 b19e14
              | (have j1 := b19e19 (M.op X1 X2) X0
                 grind)
              | exact resolve b19e14 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e206 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e15 (k X0 (τ X1))
                 have i₂ := b19e29 X1 X0
                 grind)
              | exact superpose b19e29 b19e15
              | exact resolve b19e15 b19e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e29
            have b19e250 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b19e17 (σ x) (σ x)
                 have i₂ := b19e60
                 grind)
              | exact superpose b19e60 b19e17
              | exact resolve b19e17 b19e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e253 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by
              first
              | (have i₁ := b19e250
                 have i₂ := b19e20 x x
                 grind)
              | exact superpose b19e20 b19e250
              | exact resolve b19e250 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e250
            have b19e264 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b19e32 X0 (σ x)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e32
              | exact resolve b19e32 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e320 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e14 X1 X0 X2 (σ y)
                 have i₂ := b19e264 X0
                 grind)
              | (have i₁ := b19e14 X0 (σ y) X2 X0
                 have i₂ := b19e264 X0
                 grind)
              | exact superpose b19e264 b19e14
              | exact resolve b19e14 b19e264
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e321 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op X1 (M.op (σ y) X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e14 X1 X0 (σ y) X2
                 have i₂ := b19e264 X0
                 grind)
              | (have i₁ := b19e14 X0 (σ y) X0 x
                 have i₂ := b19e264 X0
                 grind)
              | exact superpose b19e264 b19e14
              | exact resolve b19e14 b19e264
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e333 : ∀ X0 X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op X0 X2) X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e321 X0 X1 X2
                 have i₂ := b19e38 X1 X0
                 grind)
              | exact superpose b19e38 b19e321
              | exact resolve b19e321 b19e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e321
            have b19e334 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e320 X0 X1 X2
                 have i₂ := b19e32 X1 X0
                 grind)
              | exact superpose b19e32 b19e320
              | exact resolve b19e320 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e320
            have b19e383 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ (k x y)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b19e34 (σ x) X0 X1 (σ x)
                 have i₂ := b19e60
                 grind)
              | exact superpose b19e60 b19e34
              | exact resolve b19e34 b19e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e34
            have b19e446 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (k x y)) X1) := by
              intro X1
              first
              | (have i₁ := b19e383 x X1
                 have i₂ := b19e333 (σ x) X1 x
                 grind)
              | exact superpose b19e333 b19e383
              | exact resolve b19e383 b19e333
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e333 b19e383
            have b19e546 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (σ y) y)) := by
              intro X0
              first
              | (have i₁ := b19e39 X0 (M.op (σ y) x)
                 have i₂ := b19e38 y x
                 grind)
              | exact superpose b19e38 b19e39
              | exact resolve b19e39 b19e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e547 : ∀ X1 : G, (M.op X1 x) = (M.op (M.op (σ y) y) X1) := by
              intro X1
              first
              | (have i₁ := b19e33 X1 (M.op (σ y) x)
                 have i₂ := b19e38 y x
                 grind)
              | exact superpose b19e38 b19e33
              | exact resolve b19e33 b19e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e569 : ∀ X1 : G, (M.op X1 x) = (M.op X1 (σ y)) := by
              intro X1
              first
              | (have i₁ := b19e547 X1
                 have i₂ := b19e32 X1 y
                 grind)
              | exact superpose b19e32 b19e547
              | exact resolve b19e547 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e32 b19e547
            have b19e570 : ∀ X0 : G, (M.op (σ y) X0) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b19e546 X0
                 have i₂ := b19e38 X0 y
                 grind)
              | exact superpose b19e38 b19e546
              | exact resolve b19e546 b19e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e546
            have b19e719 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op (σ y) X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e40 X1 X0 X2 (σ y)
                 have i₂ := b19e264 X0
                 grind)
              | (have i₁ := b19e40 X0 (σ y) X2 X0
                 have i₂ := b19e264 X0
                 grind)
              | exact superpose b19e264 b19e40
              | exact resolve b19e40 b19e264
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e728 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (k x y))) := by
              intro X0 X1
              first
              | (have i₁ := b19e40 X0 (σ x) X1 (σ x)
                 have i₂ := b19e60
                 grind)
              | exact superpose b19e60 b19e40
              | exact resolve b19e40 b19e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e40
            have b19e809 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k x y))) := by
              intro X0
              first
              | (have i₁ := b19e728 X0 x
                 have i₂ := b19e334 (σ x) X0 x
                 grind)
              | exact superpose b19e334 b19e728
              | exact resolve b19e728 b19e334
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e728
            have b19e817 : ∀ X0 X1 X2 : G, (M.op (σ y) X1) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e719 X0 X1 X2
                 have i₂ := b19e38 X1 X0
                 grind)
              | exact superpose b19e38 b19e719
              | exact resolve b19e719 b19e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e38 b19e719
            have b19e858 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (k x y))) := by
              intro X0
              first
              | (have i₁ := b19e809 X0
                 have i₂ := b19e569 X0
                 grind)
              | exact superpose b19e569 b19e809
              | exact resolve b19e809 b19e569
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e809
            have b19e860 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op x X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e817 X0 X1 X2
                 have i₂ := b19e570 X1
                 grind)
              | exact superpose b19e570 b19e817
              | exact resolve b19e817 b19e570
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e817
            have b19e5422 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op X1 X2) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e30 x x X1 X0 X2
                 have i₂ := b19e860 (M.op x x) X0 X1
                 grind)
              | exact superpose b19e860 b19e30
              | exact resolve b19e30 b19e860
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30 b19e860
            have b19e5980 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X1))) := by
              intro X0 X1
              first
              | (have j0 := b19e55 X0 X0 x (M.op X0 X1)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e55
            have b19e5981 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (σ y))) := by
              intro X0
              first
              | (have i₁ := b19e5980 X0 x
                 have i₂ := b19e334 X0 X0 x
                 grind)
              | exact superpose b19e334 b19e5980
              | exact resolve b19e5980 b19e334
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e5980
            have b19e6059 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b19e5981 X0
                 have i₂ := b19e569 X0
                 grind)
              | exact superpose b19e569 b19e5981
              | exact resolve b19e5981 b19e569
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e5981
            have b19e6308 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op x x)) := by
              intro X0 X1
              first
              | (have i₁ := b19e6059 (M.op X0 X1)
                 have i₂ := b19e5422 x X0 X1
                 grind)
              | exact superpose b19e5422 b19e6059
              | exact resolve b19e6059 b19e5422
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e5422
            have b19e6317 : (M.op (σ y) (σ y)) = (k (σ y) (M.op x x)) := by
              first
              | (have i₁ := b19e6059 (σ y)
                 have i₂ := b19e570 x
                 grind)
              | exact superpose b19e570 b19e6059
              | exact resolve b19e6059 b19e570
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e6330 : (M.op x (σ y)) = (k (σ y) (M.op x x)) := by
              first
              | (have i₁ := b19e6317
                 have i₂ := b19e570 (σ y)
                 grind)
              | exact superpose b19e570 b19e6317
              | exact resolve b19e6317 b19e570
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e6317
            have b19e6339 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (k (M.op X0 X1) (M.op x x)) := by
              intro X0 X1
              first
              | (have i₁ := b19e6308 X0 X1
                 have i₂ := b19e334 X0 (M.op X0 X1) X1
                 grind)
              | exact superpose b19e334 b19e6308
              | exact resolve b19e6308 b19e334
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e6308
            have b19e6351 : (M.op x x) = (k (σ y) (M.op x x)) := by
              first
              | (have i₁ := b19e6330
                 have i₂ := b19e569 x
                 grind)
              | exact superpose b19e569 b19e6330
              | exact resolve b19e6330 b19e569
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e6330
            have b19e6360 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (k (M.op X0 X1) (M.op x x)) := by
              intro X0 X1
              first
              | (have i₁ := b19e6339 X0 X1
                 have i₂ := b19e264 (M.op X0 X1)
                 grind)
              | exact superpose b19e264 b19e6339
              | exact resolve b19e6339 b19e264
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e264 b19e6339
            have b19e6376 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (k (M.op X0 X1) (M.op x x)) := by
              intro X0 X1
              first
              | (have i₁ := b19e6360 X0 X1
                 have i₂ := b19e570 (M.op X0 X1)
                 grind)
              | exact superpose b19e570 b19e6360
              | exact resolve b19e6360 b19e570
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e6360
            have b19e6389 : ∀ X0 X1 : G, (M.op x (σ y)) = (k (M.op X0 X1) (M.op x x)) := by
              intro X0 X1
              first
              | (have i₁ := b19e6376 X0 X1
                 have i₂ := b19e334 X0 x X1
                 grind)
              | exact superpose b19e334 b19e6376
              | exact resolve b19e6376 b19e334
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e6376
            have b19e6398 : ∀ X0 X1 : G, (M.op x x) = (k (M.op X0 X1) (M.op x x)) := by
              intro X0 X1
              first
              | (have i₁ := b19e6389 X0 X1
                 have i₂ := b19e569 x
                 grind)
              | exact superpose b19e569 b19e6389
              | exact resolve b19e6389 b19e569
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e6389
            have b19e7405 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X2
              first
              | (have j0 := b19e79 X0 X1 X1 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e79
            have b19e7408 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e7405 X0 X1 x
                 have i₂ := b19e334 X1 X1 x
                 grind)
              | exact superpose b19e334 b19e7405
              | (have j0 := b19e7405 X0 X1 x
                 grind)
              | (have r₁ := b19e7405 (M.op X0 (σ y)) X0 x
                 have r₂ := b19e334 X0 X0 x
                 grind)
              | exact resolve b19e7405 b19e334
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e334 b19e7405
            have b19e7604 : ∀ X0 X1 : G, (M.op X1 x) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e7408 X0 X1
                 have i₂ := b19e569 X1
                 grind)
              | exact superpose b19e569 b19e7408
              | (have j0 := b19e7408 X0 X1
                 grind)
              | (have r₁ := b19e7408 (M.op X1 x) X1
                 have r₂ := b19e569 X1
                 grind)
              | exact resolve b19e7408 b19e569
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e569 b19e7408
            have b19e9317 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
              intro X0
              first
              | (have i₁ := b19e858 X0
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e858
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e858 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e858
            have b19e9433 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op y x) := by
              intro X0
              first
              | (have j0 := b19e9317 X0
                 grind)
              | (have r₁ := b19e9317 X0
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e9317 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e9317
            have b19e9459 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (M.op x y))) := by
              intro X0
              first
              | (have j0 := b19e9433 X0
                 grind)
              | (have r₁ := b19e9433 X0
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e9433 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e9433
            have b19e9472 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (M.op y x))) := by
              intro X0
              first
              | (have i₁ := b19e9459 X0
                 have i₂ := b19e42 y
                 grind)
              | exact superpose b19e42 b19e9459
              | exact resolve b19e9459 b19e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e9459
            have b19e9530 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b19e77 x x
                 have i₂ := b19e60
                 grind)
              | exact superpose b19e60 b19e77
              | exact resolve b19e77 b19e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e60
            have b19e9668 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b19e77 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e77
            have b19e9669 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b19e9668 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e9668
            have b19e9678 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by grind
            clear b19e9530
            have b19e9791 : (σ (k x y)) = (σ (k x x)) := by
              first
              | (have r₁ := b19e9678
                 have r₂ := b19e253
                 grind)
              | exact resolve b19e9678 b19e253
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e253 b19e9678
            have b19e10182 : (k x x) = (τ (σ (k x y))) := by
              first
              | (have i₁ := b19e15 (k x x)
                 have i₂ := b19e9791
                 grind)
              | exact superpose b19e9791 b19e15
              | exact resolve b19e15 b19e9791
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e9791
            have b19e10202 : (k x y) = (k x x) := by
              first
              | (have i₁ := b19e10182
                 have i₂ := b19e15 (k x y)
                 grind)
              | exact superpose b19e15 b19e10182
              | exact resolve b19e10182 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e10182
            have b19e10410 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = X1 ∨ (M.op x X1) = (k x X1) ∨ (M.op X1 x) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b19e82 X0 y y x
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e82
              | exact resolve b19e82 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e10509 : ∀ X0 X1 : G, (M.op (M.op y X1) x) = X0 ∨ (M.op (M.op y X1) X0) = (k (M.op y X1) X0) ∨ (M.op X0 (M.op y X1)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e48 (M.op y X1) x
                 have i₂ := b19e82 X0 y X1 x
                 grind)
              | (have i₁ := b19e48 X0 X1
                 have i₂ := b19e82 (M.op X0 (M.op y X1)) X1 x x
                 grind)
              | exact superpose b19e82 b19e48
              | (have j1 := b19e82 X0 y X1 x
                 grind)
              | exact resolve b19e48 b19e82
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e48 b19e82
            have b19e10601 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (k (M.op y X1) X0) ∨ (M.op X0 (M.op y X1)) = X0 := by
              intro X0 X1
              first
              | (have j0 := b19e10509 X0 X1
                 have j1 := b19e7604 X0 (M.op y X1)
                 grind)
              | (have r₁ := b19e10509 X0 X1
                 have r₂ := b19e7604 X0 (M.op y X1)
                 grind)
              | (have r₁ := b19e10509 (M.op X1 x) X1
                 have r₂ := b19e7604 (M.op (M.op y X1) x) X1
                 grind)
              | (have r₁ := b19e10509 x X1
                 have r₂ := b19e7604 (k (M.op y X1) x) (M.op y X1)
                 grind)
              | exact resolve b19e10509 b19e7604
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e10509
            have b19e10684 : ∀ X1 : G, (M.op x x) = X1 ∨ (M.op x X1) = (k x X1) ∨ (M.op X1 x) = X1 := by
              intro X1
              first
              | (have i₁ := b19e10410 x X1
                 have i₂ := b19e39 x x
                 grind)
              | exact superpose b19e39 b19e10410
              | (have j0 := b19e10410 x X1
                 grind)
              | exact resolve b19e10410 b19e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e10410
            have b19e10799 : ∀ X0 X1 : G, (M.op X0 x) = (k (M.op y X1) X0) ∨ (M.op X0 (M.op y X1)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e10601 X0 X1
                 have i₂ := b19e33 X0 X1
                 grind)
              | exact superpose b19e33 b19e10601
              | (have j0 := b19e10601 X0 X1
                 grind)
              | exact resolve b19e10601 b19e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e10601
            have b19e10881 : ∀ X1 : G, (M.op x X1) = (k x X1) ∨ (M.op X1 x) = X1 := by
              intro X1
              first
              | (have j0 := b19e10684 X1
                 have j1 := b19e7604 X1 x
                 grind)
              | (have r₁ := b19e10684 x
                 have r₂ := b19e7604 x x
                 grind)
              | (have r₁ := b19e10684 (M.op X1 x)
                 have r₂ := b19e7604 (M.op x x) X1
                 grind)
              | (have r₁ := b19e10684 x
                 have r₂ := b19e7604 (k x x) x
                 grind)
              | exact resolve b19e10684 b19e7604
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e7604 b19e10684
            have b19e10986 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (M.op X0 x) = (k (M.op y X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b19e10799 X0 X1
                 have i₂ := b19e39 X0 X1
                 grind)
              | exact superpose b19e39 b19e10799
              | (have j0 := b19e10799 X0 X1
                 grind)
              | exact resolve b19e10799 b19e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e10799
            have b19e20204 : (τ (M.op x x)) = (k y (τ (M.op x x))) := by
              first
              | (have i₁ := b19e206 y (M.op x x)
                 have i₂ := b19e6351
                 grind)
              | exact superpose b19e6351 b19e206
              | exact resolve b19e206 b19e6351
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e206 b19e6351
            have b19e20224 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
              intro X0
              first
              | (have i₁ := b19e446 X0
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e446
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e446 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e446
            have b19e20416 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op y x) := by
              intro X0
              first
              | (have j0 := b19e20224 X0
                 grind)
              | (have r₁ := b19e20224 X0
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e20224 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e20224
            have b19e20476 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x y)) X0) := by
              intro X0
              first
              | (have j0 := b19e20416 X0
                 grind)
              | (have r₁ := b19e20416 X0
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e20416 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e20416
            have b19e20514 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y x)) X0) := by
              intro X0
              first
              | (have i₁ := b19e20476 X0
                 have i₂ := b19e42 y
                 grind)
              | exact superpose b19e42 b19e20476
              | exact resolve b19e20476 b19e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e20476
            have b19e20539 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op y x)) X0) := by
              intro X0
              first
              | (have i₁ := b19e20514 X0
                 have i₂ := b19e570 X0
                 grind)
              | exact superpose b19e570 b19e20514
              | exact resolve b19e20514 b19e570
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e570 b19e20514
            have b19e33708 : ∀ X0 : G, x ≠ (M.op x x) ∨ (M.op (M.op y X0) (M.op y X0)) = (k (M.op y X0) x) := by
              intro X0
              first
              | (have i₁ := b19e68 (M.op y X0)
                 have i₂ := b19e33 x X0
                 grind)
              | exact superpose b19e33 b19e68
              | (have j0 := b19e68 x
                 grind)
              | exact resolve b19e68 b19e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e33 b19e68
            have b19e33762 : ∀ X0 : G, (M.op x (M.op y X0)) = (k (M.op y X0) x) ∨ x ≠ (M.op x x) := by
              intro X0
              first
              | (have i₁ := b19e33708 X0
                 have i₂ := b19e39 (M.op y X0) X0
                 grind)
              | exact superpose b19e39 b19e33708
              | exact resolve b19e33708 b19e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e33708
            have b19e33791 : ∀ X0 : G, (M.op x x) = (k (M.op y X0) x) ∨ x ≠ (M.op x x) := by
              intro X0
              first
              | (have i₁ := b19e33762 X0
                 have i₂ := b19e39 x X0
                 grind)
              | exact superpose b19e39 b19e33762
              | exact resolve b19e33762 b19e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e39 b19e33762
            have b19e33816 : ∀ X0 : G, (M.op x x) = (k (M.op y X0) x) := by
              intro X0
              first
              | (have j0 := b19e33791 X0
                 have j1 := b19e10986 x X0
                 grind)
              | (have r₁ := b19e33791 X0
                 have r₂ := b19e10986 x x
                 grind)
              | exact resolve b19e33791 b19e10986
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e10986 b19e33791
            have b19e34136 : (M.op x x) = (k x x) := by
              first
              | (have i₁ := b19e33816 y
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e33816
              | exact resolve b19e33816 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e33816
            have b19e34208 : (M.op x x) = (k x y) := by
              first
              | (have i₁ := b19e10202
                 have i₂ := b19e34136
                 grind)
              | exact superpose b19e34136 b19e10202
              | exact resolve b19e10202 b19e34136
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e10202 b19e34136
            have b19e34512 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b19e10881 y
                 have i₂ := b19e34208
                 grind)
              | exact superpose b19e34208 b19e10881
              | (have j0 := b19e10881 y
                 grind)
              | exact resolve b19e10881 b19e34208
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e10881 b19e34208
            have b19e34519 : (M.op x y) = (M.op x x) := by
              first
              | (have r₁ := b19e34512
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e34512 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e34512
            have b19e34529 : (M.op y x) = (M.op x x) := by
              first
              | (have i₁ := b19e34519
                 have i₂ := b19e42 y
                 grind)
              | exact superpose b19e42 b19e34519
              | exact resolve b19e34519 b19e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e42 b19e34519
            have b19e34829 : ∀ X0 X1 : G, (M.op y x) = (k (M.op X0 X1) (M.op y x)) := by
              intro X0 X1
              first
              | (have i₁ := b19e6398 X0 X1
                 have i₂ := b19e34529
                 grind)
              | exact superpose b19e34529 b19e6398
              | exact resolve b19e6398 b19e34529
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e6398
            have b19e34830 : (τ (M.op y x)) = (k y (τ (M.op y x))) := by
              first
              | (have i₁ := b19e20204
                 have i₂ := b19e34529
                 grind)
              | exact superpose b19e34529 b19e20204
              | exact resolve b19e20204 b19e34529
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e20204
            have b19e39488 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
              first
              | (have i₁ := b19e9669 (M.op y x)
                 have i₂ := b19e34829 y x
                 grind)
              | exact superpose b19e34829 b19e9669
              | (have j0 := b19e9669 (M.op y x)
                 grind)
              | exact resolve b19e9669 b19e34829
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e9669 b19e34829
            have b19e39495 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by grind
            clear b19e39488
            have b19e39504 : (σ (M.op y x)) = (M.op x (σ (M.op y x))) := by
              first
              | (have i₁ := b19e39495
                 have i₂ := b19e20539 (σ (M.op y x))
                 grind)
              | exact superpose b19e20539 b19e39495
              | exact resolve b19e39495 b19e20539
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e20539 b19e39495
            have b19e39526 : (M.op x x) = (σ (M.op y x)) := by
              first
              | (have i₁ := b19e39504
                 have i₂ := b19e9472 x
                 grind)
              | exact superpose b19e9472 b19e39504
              | exact resolve b19e39504 b19e9472
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e9472 b19e39504
            have b19e39545 : (M.op y x) = (σ (M.op y x)) := by
              first
              | (have i₁ := b19e39526
                 have i₂ := b19e34529
                 grind)
              | exact superpose b19e34529 b19e39526
              | exact resolve b19e39526 b19e34529
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e34529 b19e39526
            have b19e40892 : (M.op y x) = (τ (M.op y x)) := by
              first
              | (have i₁ := b19e15 (M.op y x)
                 have i₂ := b19e39545
                 grind)
              | exact superpose b19e39545 b19e15
              | exact resolve b19e15 b19e39545
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e39545
            have b19e42231 : (M.op y x) = (k y (M.op y x)) := by
              first
              | (have i₁ := b19e34830
                 have i₂ := b19e40892
                 grind)
              | exact superpose b19e40892 b19e34830
              | exact resolve b19e34830 b19e40892
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e34830 b19e40892
            have b19e42270 : (M.op y x) = (M.op y y) := by
              first
              | (have i₁ := b19e42231
                 have i₂ := b19e6059 y
                 grind)
              | exact superpose b19e6059 b19e42231
              | exact resolve b19e42231 b19e6059
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e6059 b19e42231
            have b19e42271 : x = (M.op y x) := by
              first
              | (have i₁ := b19e42270
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e42270
              | exact resolve b19e42270 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e42270
            have b19e42272 : False := by grind
            exact b19e42272
          · have b20e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b20e22 : y ≠ (M.op y x) := by grind
            have b20e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b20e25 : x ≠ (M.op x y) := by grind
            have b20e26 : x ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b20e20 (τ X0) X1
                 have i₂ := b20e16 X0
                 grind)
              | exact superpose b20e16 b20e20
              | exact resolve b20e20 b20e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b20e20 X1 (τ X0)
                 have i₂ := b20e16 X0
                 grind)
              | exact superpose b20e16 b20e20
              | exact resolve b20e20 b20e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e30 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
              intro X0 X1
              first
              | (have i₁ := b20e14 X0 (σ y) (σ x) X1
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e14
              | exact resolve b20e14 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e35 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ y) X0) := by
              intro X0 X1
              first
              | (have i₁ := b20e14 X0 (σ y) X1 (σ x)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e14
              | exact resolve b20e14 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e38 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 X0 X1 X2 x
                 have i₂ := b20e14 X0 X1 X3 x
                 grind)
              | (have i₁ := b20e14 (M.op X1 X2) X1 X2 X3
                 have i₂ := b20e14 (M.op X1 X3) X1 X2 X3
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e43 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b20e15 (k (τ X0) X1)
                 have i₂ := b20e28 X0 X1
                 grind)
              | exact superpose b20e28 b20e15
              | exact resolve b20e15 b20e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e54 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b20e15 (k X0 (τ X1))
                 have i₂ := b20e29 X1 X0
                 grind)
              | exact superpose b20e29 b20e15
              | exact resolve b20e15 b20e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e65 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 X1 X2 X3 X2
                 have i₂ := b20e19 X2 X0
                 grind)
              | (have i₁ := b20e14 X0 X1 X2 X3
                 have i₂ := b20e19 X0 (M.op X1 X3)
                 grind)
              | exact superpose b20e19 b20e14
              | (have j1 := b20e19 X2 X0
                 grind)
              | exact resolve b20e14 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e67 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op (M.op X1 X2) (M.op X1 X3)) = X0 ∨ (M.op X0 (M.op X1 X2)) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 (M.op X1 X2) X1 X3 X2
                 have i₂ := b20e19 (M.op X1 X2) X0
                 grind)
              | (have i₁ := b20e14 X0 X1 X2 X3
                 have i₂ := b20e19 X0 (M.op (M.op X1 X3) X0)
                 grind)
              | exact superpose b20e19 b20e14
              | (have j1 := b20e19 (M.op X1 X2) X0
                 grind)
              | exact resolve b20e14 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e91 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b20e30 X0 (σ x)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e30
              | exact resolve b20e30 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e102 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b20e14 X0 (σ y) X1 x
                 have i₂ := b20e30 X0 x
                 grind)
              | exact superpose b20e30 b20e14
              | exact resolve b20e14 b20e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e119 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e14 X1 X0 X2 (σ y)
                 have i₂ := b20e91 X0
                 grind)
              | (have i₁ := b20e14 X0 (σ y) X2 X0
                 have i₂ := b20e91 X0
                 grind)
              | exact superpose b20e91 b20e14
              | exact resolve b20e14 b20e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e120 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ y) X0)) = (M.op (M.op X0 X2) X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e14 X1 X0 (σ y) X2
                 have i₂ := b20e91 X0
                 grind)
              | (have i₁ := b20e14 X0 (σ y) X0 x
                 have i₂ := b20e91 X0
                 grind)
              | exact superpose b20e91 b20e14
              | exact resolve b20e14 b20e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e124 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b20e17 X0 (σ y)
                 have i₂ := b20e91 X0
                 grind)
              | (have i₁ := b20e17 (σ y) X0
                 have i₂ := b20e91 X0
                 grind)
              | exact superpose b20e91 b20e17
              | (have j0 := b20e17 X0 (σ y)
                 grind)
              | exact resolve b20e17 b20e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e129 : ∀ X0 X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op X0 X2) X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e120 X0 X1 X2
                 have i₂ := b20e35 X1 X0
                 grind)
              | exact superpose b20e35 b20e120
              | exact resolve b20e120 b20e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e120
            have b20e130 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e119 X0 X1 X2
                 have i₂ := b20e30 X1 X0
                 grind)
              | exact superpose b20e30 b20e119
              | exact resolve b20e119 b20e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e119
            have b20e360 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ X0 ∨ (M.op (M.op X1 X3) (M.op X1 X3)) = (k (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e17 (M.op X1 X3) X0
                 have i₂ := b20e38 X0 X1 X3 X2
                 grind)
              | (have i₁ := b20e17 (M.op X1 X3) X0
                 have i₂ := b20e38 X0 X1 X2 X3
                 grind)
              | exact superpose b20e38 b20e17
              | (have j0 := b20e17 (M.op X1 X2) X0
                 grind)
              | exact resolve b20e17 b20e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e38
            have b20e369 : ∀ X0 X1 X3 : G, (M.op X0 (σ y)) ≠ X0 ∨ (M.op (M.op X1 X3) (M.op X1 X3)) = (k (M.op X1 X3) X0) := by
              intro X0 X1 X3
              first
              | (have i₁ := b20e360 X0 X1 x X3
                 have i₂ := b20e130 X1 X0 x
                 grind)
              | exact superpose b20e130 b20e360
              | (have j0 := b20e360 X0 X1 x X3
                 grind)
              | exact resolve b20e360 b20e130
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e360
            have b20e399 : ∀ X0 X1 X3 : G, (k (M.op X1 X3) X0) = (M.op (M.op X1 X3) (σ y)) ∨ (M.op X0 (σ y)) ≠ X0 := by
              intro X0 X1 X3
              first
              | (have i₁ := b20e369 X0 X1 X3
                 have i₂ := b20e130 X1 (M.op X1 X3) X3
                 grind)
              | exact superpose b20e130 b20e369
              | (have j0 := b20e369 X0 X1 X3
                 grind)
              | exact resolve b20e369 b20e130
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e369
            have b20e411 : ∀ X0 X1 X3 : G, (k (M.op X1 X3) X0) = (M.op (σ y) (M.op X1 X3)) ∨ (M.op X0 (σ y)) ≠ X0 := by
              intro X0 X1 X3
              first
              | (have i₁ := b20e399 X0 X1 X3
                 have i₂ := b20e91 (M.op X1 X3)
                 grind)
              | exact superpose b20e91 b20e399
              | (have j0 := b20e399 X0 X1 X3
                 grind)
              | exact resolve b20e399 b20e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e399
            have b20e420 : ∀ X0 X1 X3 : G, (M.op X0 (σ y)) ≠ X0 ∨ (M.op (σ y) (σ y)) = (k (M.op X1 X3) X0) := by
              intro X0 X1 X3
              first
              | (have i₁ := b20e411 X0 X1 X3
                 have i₂ := b20e130 X1 (σ y) X3
                 grind)
              | exact superpose b20e130 b20e411
              | (have j0 := b20e411 X0 X1 X3
                 grind)
              | exact resolve b20e411 b20e130
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e411
            have b20e4307 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e19 X0 X3
                 have i₂ := b20e65 X0 X0 X1 X2
                 grind)
              | (have i₁ := b20e19 (M.op X2 X3) X1
                 have i₂ := b20e65 X0 (M.op X2 X3) X2 X3
                 grind)
              | exact superpose b20e65 b20e19
              | (have j0 := b20e19 X0 X3
                 have j1 := b20e65 X3 X1 X0 X3
                 grind)
              | exact resolve b20e19 b20e65
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e4442 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X2
              first
              | (have j0 := b20e65 X0 X1 X1 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e65
            have b20e4445 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b20e4442 X0 X1 x
                 have i₂ := b20e130 X1 X1 x
                 grind)
              | exact superpose b20e130 b20e4442
              | (have j0 := b20e4442 X0 X1 x
                 grind)
              | (have r₁ := b20e4442 (M.op X0 (σ y)) X0 x
                 have r₂ := b20e130 X0 X0 x
                 grind)
              | exact resolve b20e4442 b20e130
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e4442
            have b20e4549 : ∀ X0 X1 X3 : G, (M.op X0 (σ y)) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X3
              first
              | (have i₁ := b20e4307 X0 X1 x X3
                 have i₂ := b20e130 X1 X0 x
                 grind)
              | exact superpose b20e130 b20e4307
              | (have j0 := b20e4307 X0 X1 x X3
                 grind)
              | exact resolve b20e4307 b20e130
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e4307
            have b20e4666 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X3 X0) = X3 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1 X3
              first
              | (have j0 := b20e4549 X0 X1 X3
                 have j1 := b20e4445 X0 X1
                 grind)
              | (have r₁ := b20e4549 X1 X1 X0
                 have r₂ := b20e4445 X0 X1
                 grind)
              | (have r₁ := b20e4549 X0 X1 (M.op X1 (σ y))
                 have r₂ := b20e4445 (M.op X0 (σ y)) X1
                 grind)
              | (have r₁ := b20e4549 X1 X1 (σ y)
                 have r₂ := b20e4445 (k X1 (σ y)) X1
                 grind)
              | exact resolve b20e4549 b20e4445
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e4549
            have b20e6345 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b20e67 X0 (σ y) (σ x) x
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e67
              | exact resolve b20e67 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e6475 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = X0 ∨ (M.op (M.op (σ y) X1) X0) = (k (M.op (σ y) X1) X0) ∨ (M.op X0 (M.op (σ y) X1)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b20e102 (M.op (σ y) X1) x
                 have i₂ := b20e67 X0 (σ y) X1 x
                 grind)
              | (have i₁ := b20e102 X0 X1
                 have i₂ := b20e67 (M.op X0 (M.op (σ y) X1)) X1 x x
                 grind)
              | exact superpose b20e67 b20e102
              | (have j1 := b20e67 X0 (σ y) X1 x
                 grind)
              | exact resolve b20e102 b20e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e67 b20e102
            have b20e6571 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (k (M.op (σ y) X1) X0) ∨ (M.op X0 (M.op (σ y) X1)) = X0 := by
              intro X0 X1
              first
              | (have j0 := b20e6475 X0 X1
                 have j1 := b20e4445 X0 (M.op (σ y) X1)
                 grind)
              | (have r₁ := b20e6475 X0 X1
                 have r₂ := b20e4445 X0 (M.op (σ y) X1)
                 grind)
              | (have r₁ := b20e6475 (M.op X1 (σ y)) X1
                 have r₂ := b20e4445 (M.op (M.op (σ y) X1) (σ y)) X1
                 grind)
              | (have r₁ := b20e6475 (σ y) X1
                 have r₂ := b20e4445 (k (M.op (σ y) X1) (σ y)) (M.op (σ y) X1)
                 grind)
              | exact resolve b20e6475 b20e4445
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e6475
            have b20e6675 : ∀ X1 : G, (M.op (σ y) (σ y)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X1
              first
              | (have i₁ := b20e6345 x X1
                 have i₂ := b20e35 (σ y) x
                 grind)
              | exact superpose b20e35 b20e6345
              | (have j0 := b20e6345 x X1
                 grind)
              | exact resolve b20e6345 b20e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e6345
            have b20e6731 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (k (M.op (σ y) X1) X0) ∨ (M.op X0 (M.op (σ y) X1)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b20e6571 X0 X1
                 have i₂ := b20e30 X0 X1
                 grind)
              | exact superpose b20e30 b20e6571
              | (have j0 := b20e6571 X0 X1
                 grind)
              | exact resolve b20e6571 b20e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e6571
            have b20e6833 : ∀ X1 : G, (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
              intro X1
              first
              | (have j0 := b20e6675 X1
                 have j1 := b20e4445 X1 (σ y)
                 grind)
              | (have r₁ := b20e6675 x
                 have r₂ := b20e4445 x (σ y)
                 grind)
              | (have r₁ := b20e6675 (M.op X1 (σ y))
                 have r₂ := b20e4445 (M.op (σ y) (σ y)) X1
                 grind)
              | (have r₁ := b20e6675 (σ y)
                 have r₂ := b20e4445 (k (σ y) (σ y)) (σ y)
                 grind)
              | exact resolve b20e6675 b20e4445
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e4445 b20e6675
            have b20e6889 : ∀ X0 X1 : G, (M.op (σ y) X0) = X0 ∨ (M.op X0 (σ y)) = (k (M.op (σ y) X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b20e6731 X0 X1
                 have i₂ := b20e35 X0 X1
                 grind)
              | exact superpose b20e35 b20e6731
              | (have j0 := b20e6731 X0 X1
                 grind)
              | exact resolve b20e6731 b20e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e6731
            have b20e14201 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b20e54 y X0
                 have i₂ := b20e6833 X0
                 grind)
              | exact superpose b20e6833 b20e54
              | (have j1 := b20e6833 X0
                 grind)
              | exact resolve b20e54 b20e6833
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e54 b20e6833
            have b20e15120 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (k (M.op (σ y) X0) (σ y)) := by
              intro X0
              first
              | (have i₁ := b20e124 (M.op (σ y) X0)
                 have i₂ := b20e30 (σ y) X0
                 grind)
              | exact superpose b20e30 b20e124
              | (have j0 := b20e124 (σ y)
                 grind)
              | exact resolve b20e124 b20e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30 b20e124
            have b20e15164 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (k (M.op (σ y) X0) (σ y)) ∨ (σ y) ≠ (M.op (σ y) (σ y)) := by
              intro X0
              first
              | (have i₁ := b20e15120 X0
                 have i₂ := b20e35 (M.op (σ y) X0) X0
                 grind)
              | exact superpose b20e35 b20e15120
              | exact resolve b20e15120 b20e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e15120
            have b20e15185 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (M.op (σ y) X0) (σ y)) ∨ (σ y) ≠ (M.op (σ y) (σ y)) := by
              intro X0
              first
              | (have i₁ := b20e15164 X0
                 have i₂ := b20e35 (σ y) X0
                 grind)
              | exact superpose b20e35 b20e15164
              | exact resolve b20e15164 b20e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35 b20e15164
            have b20e15204 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (M.op (σ y) X0) (σ y)) := by
              intro X0
              first
              | (have j0 := b20e15185 X0
                 have j1 := b20e6889 (σ y) X0
                 grind)
              | (have r₁ := b20e15185 X0
                 have r₂ := b20e6889 (σ y) x
                 grind)
              | exact resolve b20e15185 b20e6889
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e6889 b20e15185
            have b20e15264 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b20e15204 (σ x)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e15204
              | exact resolve b20e15204 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e15204
            have b20e15313 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
              first
              | (have i₁ := b20e15264
                 have i₂ := b20e20 y y
                 grind)
              | exact superpose b20e20 b20e15264
              | exact resolve b20e15264 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e15264
            have b20e15478 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k y y)) X0) := by
              intro X0
              first
              | (have i₁ := b20e129 (σ y) X0 (σ y)
                 have i₂ := b20e15313
                 grind)
              | exact superpose b20e15313 b20e129
              | exact resolve b20e129 b20e15313
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e129
            have b20e15845 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (k (M.op X0 X1) (σ (k y y))) := by
              intro X0 X1
              first
              | (have i₁ := b20e420 (σ (k y y)) X0 X1
                 have i₂ := b20e15478 (σ y)
                 grind)
              | exact superpose b20e15478 b20e420
              | (have j0 := b20e420 (σ (k y y)) X0 X1
                 grind)
              | exact resolve b20e420 b20e15478
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e420 b20e15478
            have b20e15863 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (k (M.op X0 X1) (σ (k y y))) := by
              intro X0 X1
              first
              | (have j0 := b20e15845 X0 X1
                 grind)
              | (have r₁ := b20e15845 X0 X1
                 have r₂ := b20e15313
                 grind)
              | exact resolve b20e15845 b20e15313
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e15845
            have b20e15949 : ∀ X0 X1 : G, (σ (k y y)) = (k (M.op X0 X1) (σ (k y y))) := by
              intro X0 X1
              first
              | (have i₁ := b20e15863 X0 X1
                 have i₂ := b20e15313
                 grind)
              | exact superpose b20e15313 b20e15863
              | exact resolve b20e15863 b20e15313
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e15863
            have b20e24163 : ∀ X0 X1 : G, (τ (σ (k y y))) = (k (τ (M.op X0 X1)) (k y y)) := by
              intro X0 X1
              first
              | (have i₁ := b20e43 (M.op X0 X1) (k y y)
                 have i₂ := b20e15949 X0 X1
                 grind)
              | exact superpose b20e15949 b20e43
              | exact resolve b20e43 b20e15949
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e43 b20e15949
            have b20e24185 : ∀ X0 X1 : G, (k y y) = (k (τ (M.op X0 X1)) (k y y)) := by
              intro X0 X1
              first
              | (have i₁ := b20e24163 X0 X1
                 have i₂ := b20e15 (k y y)
                 grind)
              | exact superpose b20e15 b20e24163
              | exact resolve b20e24163 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e24163
            have b20e24465 : (k y y) = (k (τ (σ (k y y))) (k y y)) := by
              first
              | (have i₁ := b20e24185 (σ y) (σ y)
                 have i₂ := b20e15313
                 grind)
              | exact superpose b20e15313 b20e24185
              | exact resolve b20e24185 b20e15313
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e24185
            have b20e24509 : (k y y) = (k (k y y) (k y y)) := by
              first
              | (have i₁ := b20e24465
                 have i₂ := b20e15 (k y y)
                 grind)
              | exact superpose b20e15 b20e24465
              | exact resolve b20e24465 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e24465
            have b20e25649 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b20e4666 X0 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e4666
            have b20e25650 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b20e25649 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e25649
            have b20e25651 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b20e25650 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e25650
            have b20e25672 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b20e25651 X0
                 have j1 := b20e17 X0 X0
                 grind)
              | (have r₁ := b20e25651 X0
                 have r₂ := b20e17 X0 X0
                 grind)
              | exact resolve b20e25651 b20e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e25651
            have b20e25806 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
              intro X0
              first
              | (have i₁ := b20e20 X0 X0
                 have i₂ := b20e25672 (σ X0)
                 grind)
              | exact superpose b20e25672 b20e20
              | exact resolve b20e20 b20e25672
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e25831 : (M.op y y) = (k (M.op y y) (M.op y y)) := by
              first
              | (have i₁ := b20e24509
                 have i₂ := b20e25672 y
                 grind)
              | exact superpose b20e25672 b20e24509
              | exact resolve b20e24509 b20e25672
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e24509
            have b20e25832 : (M.op y y) = (M.op (M.op y y) (M.op y y)) := by
              first
              | (have i₁ := b20e25831
                 have i₂ := b20e25672 (M.op y y)
                 grind)
              | exact superpose b20e25672 b20e25831
              | exact resolve b20e25831 b20e25672
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e25831
            have b20e25840 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b20e25806 X0
                 have i₂ := b20e25672 X0
                 grind)
              | exact superpose b20e25672 b20e25806
              | exact resolve b20e25806 b20e25672
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e25806
            have b20e25851 : (M.op y y) = (M.op (M.op y y) (σ y)) := by
              first
              | (have i₁ := b20e25832
                 have i₂ := b20e130 y (M.op y y) y
                 grind)
              | exact superpose b20e130 b20e25832
              | exact resolve b20e25832 b20e130
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e25832
            have b20e25866 : (M.op y y) = (M.op (σ y) (M.op y y)) := by
              first
              | (have i₁ := b20e25851
                 have i₂ := b20e91 (M.op y y)
                 grind)
              | exact superpose b20e91 b20e25851
              | exact resolve b20e25851 b20e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e25851
            have b20e25879 : (M.op y y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b20e25866
                 have i₂ := b20e130 y (σ y) y
                 grind)
              | exact superpose b20e130 b20e25866
              | exact resolve b20e25866 b20e130
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e130 b20e25866
            have b20e25882 : (M.op y y) = (σ (M.op y y)) := by
              first
              | (have i₁ := b20e25879
                 have i₂ := b20e25840 y
                 grind)
              | exact superpose b20e25840 b20e25879
              | exact resolve b20e25879 b20e25840
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e25840 b20e25879
            have b20e164443 : (τ (σ y)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b20e14201 (σ x)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e14201
              | (have j0 := b20e14201 (σ x)
                 grind)
              | exact resolve b20e14201 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e14201
            have b20e164614 : (k y x) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b20e164443
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e164443
              | exact resolve b20e164443 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e164443
            have b20e164692 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b20e164614
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e164614
              | exact resolve b20e164614 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e164614
            have b20e164751 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
              first
              | (have i₁ := b20e164692
                 have i₂ := b20e91 (σ x)
                 grind)
              | exact superpose b20e91 b20e164692
              | exact resolve b20e164692 b20e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e91 b20e164692
            have b20e164804 : y = (k y x) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e164751
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e164751
              | exact resolve b20e164751 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e164751
            have b20e165026 : y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e19 y x
                 have i₂ := b20e164804
                 grind)
              | exact superpose b20e164804 b20e19
              | (have j0 := b20e19 y x
                 grind)
              | exact resolve b20e19 b20e164804
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e164804
            have b20e165047 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
              first
              | (have r₁ := b20e165026
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e165026 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e165026
            have b20e165069 : x = (M.op x y) ∨ (σ x) = (σ y) := by
              first
              | (have r₁ := b20e165047
                 have r₂ := b20e26
                 grind)
              | exact resolve b20e165047 b20e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e165047
            have b20e165081 : (σ x) = (σ y) := by
              first
              | (have r₁ := b20e165069
                 have r₂ := b20e25
                 grind)
              | exact resolve b20e165069 b20e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e165069
            have b20e165083 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b20e21
                 have i₂ := b20e165081
                 grind)
              | exact superpose b20e165081 b20e21
              | exact resolve b20e21 b20e165081
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e165093 : x = (τ (σ y)) := by
              first
              | (have i₁ := b20e15 x
                 have i₂ := b20e165081
                 grind)
              | exact superpose b20e165081 b20e15
              | exact resolve b20e15 b20e165081
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e165081
            have b20e165233 : x = y := by
              first
              | (have i₁ := b20e165093
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e165093
              | exact resolve b20e165093 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e165093
            have b20e165240 : (σ (M.op x y)) ≠ (σ (k y y)) := by
              first
              | (have i₁ := b20e165083
                 have i₂ := b20e15313
                 grind)
              | exact superpose b20e15313 b20e165083
              | exact resolve b20e165083 b20e15313
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e15313 b20e165083
            have b20e165276 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
              first
              | (have i₁ := b20e165240
                 have i₂ := b20e25672 y
                 grind)
              | exact superpose b20e25672 b20e165240
              | exact resolve b20e165240 b20e25672
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e25672 b20e165240
            have b20e165310 : (σ (M.op x y)) ≠ (M.op y y) := by
              first
              | (have i₁ := b20e165276
                 have i₂ := b20e25882
                 grind)
              | exact superpose b20e25882 b20e165276
              | exact resolve b20e165276 b20e25882
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e165276
            have b20e165340 : (M.op y y) ≠ (σ (M.op y y)) := by
              first
              | (have i₁ := b20e165310
                 have i₂ := b20e165233
                 grind)
              | exact superpose b20e165233 b20e165310
              | exact resolve b20e165310 b20e165233
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e165233 b20e165310
            have b20e165352 : False := by grind
            exact b20e165352
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : y ≠ (M.op y x) := by grind
            have b21e23 : y ≠ (M.op x x) := by grind
            have b21e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b21e25 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b21e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e34 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 x) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X0 x y X1
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e43 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b21e34 X0 y
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e34
              | exact resolve b21e34 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e34
            have b21e88 : y ≠ (M.op x y) := by
              first
              | (have i₁ := b21e22
                 have i₂ := b21e43 y
                 grind)
              | exact superpose b21e43 b21e22
              | exact resolve b21e22 b21e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e43
            have b21e102 : x ≠ y := by
              first
              | (have i₁ := b21e88
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e88
              | exact resolve b21e88 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e88
            have b21e107 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
            have b21e109 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e107
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e107 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e107
            have b21e112 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b21e109
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e109
              | exact resolve b21e109 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e109
            have b21e128 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e112
                 grind)
              | exact superpose b21e112 b21e15
              | exact resolve b21e15 b21e112
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e112
            have b21e129 : y = (k x y) := by
              first
              | (have i₁ := b21e128
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e128
              | exact resolve b21e128 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e128
            have b21e136 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e129
                 grind)
              | exact superpose b21e129 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e129
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e129
            have b21e137 : y = (M.op x y) ∨ y = (M.op y x) := by
              first
              | (have r₁ := b21e136
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e136 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e136
            have b21e139 : y = (M.op x y) := by
              first
              | (have r₁ := b21e137
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e137 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e137
            have b21e141 : x = y := by
              first
              | (have i₁ := b21e139
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e139
              | exact resolve b21e139 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e139
            have b21e143 : False := by grind
            exact b21e143
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : y ≠ (M.op y x) := by grind
              have b22e24 : y ≠ (M.op x x) := by grind
              have b22e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b22e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              have b22e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e39 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 x) := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X0 y y X1
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e15
                | exact resolve b22e15 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e48 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b22e39 X0 y
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e39
                | exact resolve b22e39 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e39
              have b22e68 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b22e23
                   have i₂ := b22e48 y
                   grind)
                | exact superpose b22e48 b22e23
                | exact resolve b22e23 b22e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e48
              have b22e105 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
              have b22e111 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e105
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e105 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e105
              have b22e116 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b22e111
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e111
                | exact resolve b22e111 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e111
              have b22e134 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e116
                   grind)
                | exact superpose b22e116 b22e16
                | exact resolve b22e16 b22e116
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e116
              have b22e135 : y = (k x y) := by
                first
                | (have i₁ := b22e134
                   have i₂ := b22e16 y
                   grind)
                | exact superpose b22e16 b22e134
                | exact resolve b22e134 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e134
              have b22e141 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e135
                   grind)
                | exact superpose b22e135 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e135
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e135
              have b22e142 : y = (M.op x x) ∨ y = (M.op y x) := by
                first
                | (have r₁ := b22e141
                   have r₂ := b22e68
                   grind)
                | exact resolve b22e141 b22e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e68 b22e141
              have b22e144 : y = (M.op y x) := by
                first
                | (have r₁ := b22e142
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e142 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e142
              have b22e146 : False := by grind
              exact b22e146
            · have b23e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : y ≠ (M.op y x) := by grind
              have b23e24 : y ≠ (M.op x x) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b23e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e94 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
              have b23e101 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e94
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e94 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e94
              have b23e102 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b23e101
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e101
                | exact resolve b23e101 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e101
              have b23e108 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e102
                   grind)
                | exact superpose b23e102 b23e16
                | exact resolve b23e16 b23e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e102
              have b23e109 : y = (k x y) := by
                first
                | (have i₁ := b23e108
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e108
                | exact resolve b23e108 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e108
              have b23e144 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e109
                   grind)
                | exact superpose b23e109 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e109
              have b23e145 : y = (M.op x y) ∨ y = (M.op y x) := by
                first
                | (have r₁ := b23e144
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e144 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e144
              have b23e147 : y = (M.op x y) := by
                first
                | (have r₁ := b23e145
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e145 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e145
              have b23e197 : ∀ X0 X1 : G, (M.op y X0) = (M.op X0 (M.op x X1)) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X0 x X1 y
                   have i₂ := b23e147
                   grind)
                | exact superpose b23e147 b23e15
                | exact resolve b23e15 b23e147
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e965 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b23e197 X0 y
                   have i₂ := b23e147
                   grind)
                | exact superpose b23e147 b23e197
                | exact resolve b23e197 b23e147
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e197
              have b23e1815 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b23e23
                   have i₂ := b23e965 x
                   grind)
                | exact superpose b23e965 b23e23
                | exact resolve b23e23 b23e965
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e965
              have b23e1848 : False := by grind
              exact b23e1848
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b24e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : y ≠ (M.op y x) := by grind
            have b24e23 : y ≠ (M.op x x) := by grind
            have b24e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b24e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b24e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e28 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e21
              | exact resolve b24e21 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e72 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b24e25
                 have i₂ := b24e19 (σ x) X0
                 grind)
              | (have i₁ := b24e25
                 have i₂ := b24e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b24e19 b24e25
              | (have j1 := b24e19 (σ x) X0
                 grind)
              | (have r₁ := b24e25
                 have r₂ := b24e19 (σ x) (σ y)
                 grind)
              | exact resolve b24e25 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e4195 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b24e72 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e72
            have b24e4196 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b24e4195
                 have r₂ := b24e24
                 grind)
              | exact resolve b24e4195 b24e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4195
            have b24e4197 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b24e4196
                 have i₂ := b24e20 x y
                 grind)
              | exact superpose b24e20 b24e4196
              | exact resolve b24e4196 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4196
            have b24e4535 : (σ x) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b24e28
                 have i₂ := b24e4197
                 grind)
              | exact superpose b24e4197 b24e28
              | exact resolve b24e28 b24e4197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e28 b24e4197
            have b24e4591 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b24e4535
                 have i₂ := b24e19 x y
                 grind)
              | exact superpose b24e19 b24e4535
              | (have j1 := b24e19 x y
                 grind)
              | exact resolve b24e4535 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4535
            have b24e4592 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
              first
              | (have r₁ := b24e4591
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e4591 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4591
            have b24e4594 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have r₁ := b24e4592
                 have r₂ := b24e22
                 grind)
              | exact resolve b24e4592 b24e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4592
            have b24e4597 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b24e4594
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e4594
              | exact resolve b24e4594 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4594
            have b24e4598 : False := by grind
            exact b24e4598
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e23 : y ≠ (M.op y x) := by grind
              have b25e24 : y ≠ (M.op x x) := by grind
              have b25e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b25e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e87 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b25e26
                   have i₂ := b25e20 (σ x) X0
                   grind)
                | (have i₁ := b25e26
                   have i₂ := b25e20 X0 (M.op (σ x) (σ x))
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
              have b25e4974 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b25e87 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e87
              have b25e4975 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b25e4974
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e4974 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4974
              have b25e4976 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b25e4975
                   have i₂ := b25e21 x y
                   grind)
                | exact superpose b25e21 b25e4975
                | exact resolve b25e4975 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4975
              have b25e6122 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e4976
                   grind)
                | exact superpose b25e4976 b25e22
                | exact resolve b25e22 b25e4976
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4976
              have b25e6926 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e6122
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e6122
                | (have j1 := b25e20 x y
                   grind)
                | exact resolve b25e6122 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6122
              have b25e6927 : y = (M.op x x) ∨ y = (M.op y x) := by grind
              clear b25e6926
              have b25e6929 : y = (M.op y x) := by
                first
                | (have r₁ := b25e6927
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e6927 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6927
              have b25e6931 : False := by grind
              exact b25e6931
            · have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : y ≠ (M.op y x) := by grind
              have b26e24 : y ≠ (M.op x x) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b26e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e75 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b26e26
                   have i₂ := b26e20 (σ x) X0
                   grind)
                | (have i₁ := b26e26
                   have i₂ := b26e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b26e20 b26e26
                | (have j1 := b26e20 (σ x) X0
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ x) (σ y)
                   grind)
                | exact resolve b26e26 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1780 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b26e75 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e75
              have b26e1781 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b26e1780
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e1780 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1780
              have b26e1782 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e1781
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e1781
                | exact resolve b26e1781 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1781
              have b26e1783 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e1782
                   grind)
                | exact superpose b26e1782 b26e22
                | exact resolve b26e22 b26e1782
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1782
              have b26e1870 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b26e1783
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e1783
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e1783 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1783
              have b26e1871 : y = (M.op x x) ∨ y = (M.op y x) := by grind
              clear b26e1870
              have b26e1873 : y = (M.op y x) := by
                first
                | (have r₁ := b26e1871
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e1871 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1871
              have b26e1875 : False := by grind
              exact b26e1875
