import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4434`: `x ◇ (y ◇ x) = (x ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_x_pxx_pyx_Equation4434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
          intro X0 X1 X2
          grind
        have b0e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op y y) := by grind
        have b0e21 : (σ y) = (M.op (σ y) (σ y)) := by grind
        have b0e22 : x = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e25 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
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
        have b0e28 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b0e25 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e25
        have b0e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e18 (τ X0) X1
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e18
          | exact resolve b0e18 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e36 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b0e12 (σ y) (σ y) x
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e12
          | exact resolve b0e12 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e37 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
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
        have b0e38 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e12 y y x
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e45 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e12 X0 X1 x
             have i₂ := b0e12 X0 X2 x
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e48 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e38 X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e38
          | exact resolve b0e38 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38
        have b0e49 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e37 X0
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e37
          | exact resolve b0e37 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e37
        have b0e50 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b0e36 X0
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e36
          | exact resolve b0e36 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36
        have b0e159 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b0e30 X0 x
             have i₂ := b0e28 (τ X0)
             grind)
          | exact superpose b0e28 b0e30
          | exact resolve b0e30 b0e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e28 b0e30
        have b0e165 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b0e159 X0
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e159
          | exact resolve b0e159 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e159
        have b0e171 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b0e165
        have b0e175 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b0e171
        have b0e317 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b0e45 X0 X1 (σ y)
             have i₂ := b0e50 X0
             grind)
          | exact superpose b0e50 b0e45
          | exact resolve b0e45 b0e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e50
        have b0e324 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b0e45 X0 X1 y
             have i₂ := b0e48 X0
             grind)
          | exact superpose b0e48 b0e45
          | exact resolve b0e45 b0e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e45 b0e48
        have b0e368 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e317 X0 x
             have i₂ := b0e324 X0 x
             grind)
          | exact superpose b0e324 b0e317
          | exact resolve b0e317 b0e324
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e317 b0e324
        have b0e507 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e368 (σ x)
             grind)
          | exact superpose b0e368 b0e19
          | exact resolve b0e19 b0e368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e368
        have b0e511 : (σ x) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b0e507
             have i₂ := b0e49 y
             grind)
          | exact superpose b0e49 b0e507
          | exact resolve b0e507 b0e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e49 b0e507
        have b0e1101 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e12 (σ x) (σ x) x
             have i₂ := b0e175
             grind)
          | exact superpose b0e175 b0e12
          | exact resolve b0e12 b0e175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e1103 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e1101 X0
             have i₂ := b0e175
             grind)
          | exact superpose b0e175 b0e1101
          | exact resolve b0e1101 b0e175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e175 b0e1101
        have b0e1234 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b0e511
             have i₂ := b0e1103 y
             grind)
          | exact superpose b0e1103 b0e511
          | (have r₁ := b0e511
             have r₂ := b0e1103 y
             grind)
          | exact resolve b0e511 b0e1103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e511 b0e1103
        have b0e1259 : False := by grind
        exact b0e1259
      · rcases eq_or_ne (y) (x) with h2b | h2b
        · have b1e21 : y = (M.op y y) := by grind
          have b1e23 : x ≠ (M.op x x) := by grind
          have b1e24 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e28 : False := by grind
          exact b1e28
        · have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e23 : x ≠ (M.op x x) := by grind
          have b2e24 : x ≠ y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 (τ X0) X1
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e19
            | exact resolve b2e19 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b2e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b2e81 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e16 X1 X0
               have i₂ := b2e18 X2 X0
               grind)
            | exact superpose b2e18 b2e16
            | (have j0 := b2e16 X1 X0
               have j1 := b2e18 X2 X0
               grind)
            | (have r₁ := b2e16 X0 X1
               have r₂ := b2e18 X0 X1
               grind)
            | (have r₁ := b2e16 X0 X1
               have r₂ := b2e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b2e16 X0 X0
               have r₂ := b2e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b2e16 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e84 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (k X1 X0) = X1 ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b2e81 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e81
          have b2e114 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b2e30 X1 X0
               have i₂ := b2e18 (τ X1) X0
               grind)
            | exact superpose b2e18 b2e30
            | (have j1 := b2e18 (M.op X0 X0) X0
               grind)
            | exact resolve b2e30 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e119 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k (τ X0) X1)
               have i₂ := b2e30 X0 X1
               grind)
            | exact superpose b2e30 b2e14
            | exact resolve b2e14 b2e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e30
          have b2e1044 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e19 X1 X0
               have i₂ := b2e84 (σ X0) X2 (σ X1)
               grind)
            | exact superpose b2e84 b2e19
            | (have j1 := b2e84 (σ X0) X2 (σ X1)
               grind)
            | exact resolve b2e19 b2e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e84
          have b2e2150 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b2e58 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e58
          have b2e3215 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e119 X1 (τ X0)
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e119
            | exact resolve b2e119 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e119
          have b2e6866 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b2e2150 (τ X0)
               have i₂ := b2e31 X0 (τ X0)
               grind)
            | exact superpose b2e31 b2e2150
            | (have j0 := b2e2150 (τ X0)
               grind)
            | exact resolve b2e2150 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e31 b2e2150
          have b2e6883 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b2e6866 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e6866
            | (have j0 := b2e6866 X0
               grind)
            | exact resolve b2e6866 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e6866
          have b2e6892 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e6883 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e6883
            | (have j0 := b2e6883 X0
               grind)
            | exact resolve b2e6883 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e6883
          have b2e6914 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b2e6892 (τ X0)
               have i₂ := b2e3215 X0 X0
               grind)
            | exact superpose b2e3215 b2e6892
            | (have j0 := b2e6892 (τ X0)
               grind)
            | exact resolve b2e6892 b2e3215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e3215 b2e6892
          have b2e8072 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e114 X0 (σ X0)
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e114
            | (have j0 := b2e114 X1 X1
               grind)
            | exact resolve b2e114 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e114
          have b2e8242 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e8072 X0 X1
               have i₂ := b2e19 X0 X1
               grind)
            | exact superpose b2e19 b2e8072
            | (have j0 := b2e8072 (M.op X1 X1) X1
               grind)
            | exact resolve b2e8072 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e8072
          have b2e11921 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b2e20
               have i₂ := b2e1044 x y X0
               grind)
            | exact superpose b2e1044 b2e20
            | (have j1 := b2e1044 x y X0
               grind)
            | exact resolve b2e20 b2e1044
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1044
          have b2e118907 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b2e11921 X0
               have i₂ := b2e8242 y x
               grind)
            | exact superpose b2e8242 b2e11921
            | (have j0 := b2e11921 X0
               have j1 := b2e8242 (M.op x x) x
               grind)
            | (have r₁ := b2e11921 X0
               have r₂ := b2e8242 y x
               grind)
            | (have r₁ := b2e11921 X0
               have r₂ := b2e8242 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b2e11921 X0
               have r₂ := b2e8242 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b2e11921 b2e8242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e8242 b2e11921
          have b2e118909 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
            intro X0
            first
            | (have j0 := b2e118907 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e118907
          have b2e118922 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
            intro X0
            first
            | (have j0 := b2e118909 X0
               grind)
            | (have r₁ := b2e118909 X0
               have r₂ := b2e23
               grind)
            | exact resolve b2e118909 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e118909
          have b2e118932 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b2e118922 X0
               grind)
            | (have r₁ := b2e118922 X0
               have r₂ := b2e24
               grind)
            | exact resolve b2e118922 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e118922
          have b2e119006 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e6914 (σ x)
               have i₂ := b2e118932 (σ x)
               grind)
            | exact superpose b2e118932 b2e6914
            | (have j0 := b2e6914 (σ x)
               grind)
            | exact resolve b2e6914 b2e118932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e6914 b2e118932
          have b2e119114 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (σ y) := by grind
          clear b2e119006
          have b2e119156 : x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e119114
               have i₂ := b2e14 x
               grind)
            | exact superpose b2e14 b2e119114
            | exact resolve b2e119114 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e119114
          have b2e119180 : (σ x) = (σ y) := by
            first
            | (have r₁ := b2e119156
               have r₂ := b2e23
               grind)
            | exact resolve b2e119156 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e119156
          have b2e119484 : x = (τ (σ y)) := by
            first
            | (have i₁ := b2e14 x
               have i₂ := b2e119180
               grind)
            | exact superpose b2e119180 b2e14
            | exact resolve b2e14 b2e119180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e119180
          have b2e119604 : x = y := by
            first
            | (have i₁ := b2e119484
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e119484
            | exact resolve b2e119484 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e119484
          have b2e119626 : False := by grind
          exact b2e119626
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : y = (M.op y y) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e30 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b3e16 X0 y
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e16
            | (have j0 := b3e16 X0 y
               grind)
            | (have r₁ := b3e16 X0 y
               have r₂ := b3e21
               grind)
            | exact resolve b3e16 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e33 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b3e30 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e30
          have b3e35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b3e109 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b3e35 X0 y
               have i₂ := b3e33 (τ X0)
               grind)
            | exact superpose b3e33 b3e35
            | exact resolve b3e35 b3e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e33 b3e35
          have b3e116 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b3e109 X0
               have i₂ := b3e15 X0
               grind)
            | exact superpose b3e15 b3e109
            | exact resolve b3e109 b3e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e109
          have b3e131 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b3e116
          have b3e135 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b3e131
          have b3e139 : False := by grind
          exact b3e139
        · rcases eq_or_ne (y) (x) with h2b | h2b
          · have b4e22 : y = (M.op y y) := by grind
            have b4e25 : x ≠ (M.op x x) := by grind
            have b4e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e31 : False := by grind
            exact b4e31
          · have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e24 : (σ x) = (σ y) := by grind
            have b5e26 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e29 : x = (τ (σ y)) := by
              first
              | (have i₁ := b5e15 x
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e15
              | exact resolve b5e15 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e30 : x = y := by
              first
              | (have i₁ := b5e29
                 have i₂ := b5e15 y
                 grind)
              | exact superpose b5e15 b5e29
              | exact resolve b5e29 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e29
            have b5e31 : False := by grind
            exact b5e31
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op y y) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
          have b6e29 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b6e26 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26
          have b6e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b6e138 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e30 X0 y
               have i₂ := b6e29 (τ X0)
               grind)
            | exact superpose b6e29 b6e30
            | exact resolve b6e30 b6e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e29 b6e30
          have b6e142 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e138 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e138
            | exact resolve b6e138 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e138
          have b6e160 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b6e142
          have b6e163 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b6e160
          have b6e167 : False := by grind
          exact b6e167
        · rcases eq_or_ne (y) (x) with h2b | h2b
          · have b7e24 : (σ x) ≠ (σ y) := by grind
            have b7e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e31 : False := by grind
            exact b7e31
          · have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op y y) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e28 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
            have b8e29 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b8e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e28
            have b8e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
            have b8e92 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e30 X0 y
                 have i₂ := b8e29 (τ X0)
                 grind)
              | exact superpose b8e29 b8e30
              | exact resolve b8e30 b8e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e29 b8e30
            have b8e99 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e92 X0
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e92
              | exact resolve b8e92 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e92
            have b8e114 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b8e99
            have b8e118 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b8e114
            have b8e122 : False := by grind
            exact b8e122
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e21 : y ≠ (M.op y y) := by grind
          have b9e22 : x = y := by grind
          have b9e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e28 : False := by grind
          exact b9e28
        · rcases eq_or_ne (y) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e23 : x = y := by grind
            have b10e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            have b10e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e32 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b10e17 X0 (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 X0 (σ y)
                 grind)
              | (have r₁ := b10e17 X0 (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e33 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b10e32 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e32
            have b10e37 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b10e33 (σ X0)
                 have i₂ := b10e20 X0 y
                 grind)
              | exact superpose b10e20 b10e33
              | exact resolve b10e33 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e33
            have b10e40 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b10e15 (k X0 y)
                 have i₂ := b10e37 X0
                 grind)
              | exact superpose b10e37 b10e15
              | exact resolve b10e15 b10e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e37
            have b10e41 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b10e40 X0
                 have i₂ := b10e15 X0
                 grind)
              | exact superpose b10e15 b10e40
              | exact resolve b10e40 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e40
            have b10e60 : y = (M.op y y) ∨ y = (M.op y y) := by grind
            clear b10e41
            have b10e62 : y = (M.op y y) := by grind
            clear b10e60
            have b10e67 : False := by grind
            exact b10e67
          · have b11e23 : x = y := by grind
            have b11e26 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e31 : False := by grind
            exact b11e31
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e22 : y ≠ (M.op y y) := by grind
            have b12e23 : x = y := by grind
            have b12e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e31 : False := by grind
            exact b12e31
          · rcases eq_or_ne (y) (x) with h2b | h2b
            · have b13e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e24 : x = y := by grind
              have b13e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b13e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                grind
              have b13e741 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b13e49
              have b13e764 : (σ (M.op y y)) ≠ (σ (k y y)) := by
                first
                | (have r₁ := b13e741
                   have r₂ := b13e25
                   grind)
                | exact resolve b13e741 b13e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e741
              have b13e767 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
              clear b13e764
              have b13e769 : y = (M.op y y) := by grind
              clear b13e767
              have b13e770 : False := by grind
              exact b13e770
            · have b14e24 : x = y := by grind
              have b14e28 : x ≠ y := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e34 : False := by grind
              exact b14e34
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e23 : x = y := by grind
            have b15e25 : (σ x) ≠ (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e31 : False := by grind
            exact b15e31
          · rcases eq_or_ne (y) (x) with h2b | h2b
            · have b16e24 : x = y := by grind
              have b16e26 : (σ x) ≠ (σ y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e34 : False := by grind
              exact b16e34
            · have b17e24 : x = y := by grind
              have b17e28 : x ≠ y := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e34 : False := by grind
              exact b17e34
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : y ≠ (M.op y y) := by grind
          have b18e23 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e27 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b18e16 X0 (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e16
            | (have j0 := b18e16 X0 (σ y)
               grind)
            | (have r₁ := b18e16 X0 (σ y)
               have r₂ := b18e23
               grind)
            | exact resolve b18e16 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b18e27 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e27
          have b18e33 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
            intro X0
            first
            | (have i₁ := b18e19 X0 y
               have i₂ := b18e28 (σ X0)
               grind)
            | exact superpose b18e28 b18e19
            | exact resolve b18e19 b18e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e28
          have b18e91 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b18e14 (k X0 y)
               have i₂ := b18e33 X0
               grind)
            | exact superpose b18e33 b18e14
            | exact resolve b18e14 b18e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e33
          have b18e92 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b18e91 X0
               have i₂ := b18e14 X0
               grind)
            | exact superpose b18e14 b18e91
            | exact resolve b18e91 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e91
          have b18e124 : y = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b18e92
          have b18e126 : y = (M.op y y) := by grind
          clear b18e124
          have b18e129 : False := by grind
          exact b18e129
        · rcases eq_or_ne (y) (x) with h2b | h2b
          · have b19e23 : x ≠ y := by grind
            have b19e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e31 : False := by grind
            exact b19e31
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op y y) := by grind
            have b20e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
            have b20e29 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b20e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e33 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b20e20 X0 y
                 have i₂ := b20e29 (σ X0)
                 grind)
              | exact superpose b20e29 b20e20
              | exact resolve b20e20 b20e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e36 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b20e15 (k X0 y)
                 have i₂ := b20e33 X0
                 grind)
              | exact superpose b20e33 b20e15
              | exact resolve b20e15 b20e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e33
            have b20e37 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b20e36 X0
                 have i₂ := b20e15 X0
                 grind)
              | exact superpose b20e15 b20e36
              | exact resolve b20e36 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e36
            have b20e56 : y = (M.op y y) ∨ y = (M.op y y) := by grind
            clear b20e37
            have b20e58 : y = (M.op y y) := by grind
            clear b20e56
            have b20e63 : False := by grind
            exact b20e63
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e23 : x ≠ y := by grind
            have b21e25 : (σ x) = (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e29 : x = (τ (σ y)) := by
              first
              | (have i₁ := b21e15 x
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e15
              | exact resolve b21e15 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e30 : x = y := by
              first
              | (have i₁ := b21e29
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e29
              | exact resolve b21e29 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e29
            have b21e31 : False := by grind
            exact b21e31
          · rcases eq_or_ne (y) (x) with h2b | h2b
            · have b22e24 : x ≠ y := by grind
              have b22e28 : x = y := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e34 : False := by grind
              exact b22e34
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e26 : (σ x) = (σ y) := by grind
              have b23e28 : x ≠ y := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e31 : x = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 x
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e16
                | exact resolve b23e16 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e32 : x = y := by
                first
                | (have i₁ := b23e31
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e31
                | exact resolve b23e31 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e31
              have b23e33 : False := by grind
              exact b23e33
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
              intro X0 X1 X2
              grind
            have b24e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e28 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b24e17 X0 x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e17
              | (have j0 := b24e17 X0 x
                 grind)
              | (have r₁ := b24e17 X0 x
                 have r₂ := b24e26
                 grind)
              | exact resolve b24e17 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e29 : ∀ X0 : G, (k X0 x) = X0 := by
              intro X0
              first
              | (have j0 := b24e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e28
            have b24e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 (τ X0) X1
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e32 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
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
              | (have i₁ := b24e32 X0
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e32
              | exact resolve b24e32 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32
            have b24e92 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b24e30 X0 x
                 have i₂ := b24e29 (τ X0)
                 grind)
              | exact superpose b24e29 b24e30
              | exact resolve b24e30 b24e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e29 b24e30
            have b24e99 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b24e92 X0
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e92
              | exact resolve b24e92 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e92
            have b24e114 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b24e99
            have b24e118 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b24e114
            have b24e228 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b24e14 (σ x) (σ x) x
                 have i₂ := b24e118
                 grind)
              | exact superpose b24e118 b24e14
              | exact resolve b24e14 b24e118
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e230 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b24e228 X0
                 have i₂ := b24e118
                 grind)
              | exact superpose b24e118 b24e228
              | exact resolve b24e228 b24e118
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e118 b24e228
            have b24e407 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e230 (σ y)
                 grind)
              | exact superpose b24e230 b24e21
              | exact resolve b24e21 b24e230
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e230
            have b24e431 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b24e407
                 have i₂ := b24e42 y
                 grind)
              | exact superpose b24e42 b24e407
              | exact resolve b24e407 b24e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e42 b24e407
            have b24e432 : False := by grind
            exact b24e432
          · rcases eq_or_ne (y) (x) with h2b | h2b
            · have b25e26 : (σ x) ≠ (σ y) := by grind
              have b25e28 : x = y := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e34 : False := by grind
              exact b25e34
            · have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e26 : (σ x) ≠ (σ y) := by grind
              have b26e27 : x ≠ (M.op x x) := by grind
              have b26e28 : x ≠ y := by grind
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
              have b26e49 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k X0 (τ X1))
                   have i₂ := b26e31 X1 X0
                   grind)
                | exact superpose b26e31 b26e16
                | exact resolve b26e16 b26e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                grind
              have b26e75 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e18 X1 X0
                   have i₂ := b26e20 X2 X0
                   grind)
                | exact superpose b26e20 b26e18
                | (have j0 := b26e18 X1 X0
                   have j1 := b26e20 X2 X0
                   grind)
                | (have r₁ := b26e18 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e18 X0 X1
                   have r₂ := b26e20 (M.op X1 X1) X1
                   grind)
                | (have r₁ := b26e18 X0 X0
                   have r₂ := b26e20 X0 (M.op X0 X0)
                   grind)
                | exact resolve b26e18 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e80 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (k X1 X0) = X1 ∨ X0 = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e75 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e75
              have b26e436 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X0)) = X2 ∨ (σ X0) = (σ X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e80 (σ X0) X2 (σ X1)
                   grind)
                | exact superpose b26e80 b26e21
                | (have j1 := b26e80 (σ X0) X2 (σ X1)
                   grind)
                | exact resolve b26e21 b26e80
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e80
              have b26e898 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e53 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e53
              have b26e11588 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
                intro X0
                first
                | (have i₁ := b26e898 (τ X0)
                   have i₂ := b26e31 X0 (τ X0)
                   grind)
                | exact superpose b26e31 b26e898
                | (have j0 := b26e898 (τ X0)
                   grind)
                | exact resolve b26e898 b26e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e31 b26e898
              have b26e11622 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
                intro X0
                first
                | (have i₁ := b26e11588 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e11588
                | (have j0 := b26e11588 X0
                   grind)
                | exact resolve b26e11588 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11588
              have b26e11636 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have i₁ := b26e11622 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e11622
                | (have j0 := b26e11622 X0
                   grind)
                | exact resolve b26e11622 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11622
              have b26e30799 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have i₁ := b26e22
                   have i₂ := b26e436 x y X0
                   grind)
                | exact superpose b26e436 b26e22
                | (have j1 := b26e436 x y X0
                   grind)
                | exact resolve b26e22 b26e436
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e436
              have b26e30911 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have j0 := b26e30799 X0
                   grind)
                | (have r₁ := b26e30799 X0
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e30799 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30799
              have b26e268923 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) ∨ x = y := by
                intro X0
                first
                | (have i₁ := b26e30911 X0
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e30911
                | (have j0 := b26e30911 X0
                   have j1 := b26e20 (M.op x x) x
                   grind)
                | (have r₁ := b26e30911 X0
                   have r₂ := b26e20 (σ (M.op x y)) (σ (k y x))
                   grind)
                | (have r₁ := b26e30911 X0
                   have r₂ := b26e20 (σ (k y x)) (σ (M.op x y))
                   grind)
                | exact resolve b26e30911 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30911
              have b26e268927 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) ∨ x = y := by
                intro X0
                first
                | (have j0 := b26e268923 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e268923
              have b26e268929 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = y := by
                intro X0
                first
                | (have j0 := b26e268927 X0
                   grind)
                | (have r₁ := b26e268927 X0
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e268927 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e268927
              have b26e268930 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have j0 := b26e268929 X0
                   grind)
                | (have r₁ := b26e268929 X0
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e268929 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e268929
              have b26e268975 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) := by
                intro X0
                first
                | (have i₁ := b26e49 X0 (σ x)
                   have i₂ := b26e268930 (σ X0)
                   grind)
                | exact superpose b26e268930 b26e49
                | exact resolve b26e49 b26e268930
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e49 b26e268930
              have b26e268992 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
                intro X0
                first
                | (have i₁ := b26e268975 X0
                   have i₂ := b26e16 x
                   grind)
                | exact superpose b26e16 b26e268975
                | exact resolve b26e268975 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e268975
              have b26e269001 : ∀ X0 : G, (k X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b26e268992 X0
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e268992
                | exact resolve b26e268992 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e268992
              have b26e269607 : x ≠ x ∨ x = (M.op x x) := by
                first
                | (have i₁ := b26e11636 x
                   have i₂ := b26e269001 x
                   grind)
                | exact superpose b26e269001 b26e11636
                | (have j0 := b26e11636 x
                   grind)
                | (have r₁ := b26e11636 x
                   have r₂ := b26e269001 x
                   grind)
                | exact resolve b26e11636 b26e269001
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11636 b26e269001
              have b26e269642 : x = (M.op x x) := by grind
              clear b26e269607
              have b26e269659 : False := by grind
              exact b26e269659

/-- `Equation4434`: `x ◇ (y ◇ x) = (x ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyy_pxy_Equation4434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e73 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e78 : False := by grind
      exact b0e78
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : False := by grind
        exact b1e26
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e26 : False := by grind
        exact b2e26
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
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
          have b4e34 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) (σ y) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e13 y y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e13 X0 X2 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e35 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e35
            | exact resolve b4e35 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e44 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e34 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e58 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ y) X1
               have i₂ := b4e44 X0
               grind)
            | exact superpose b4e44 b4e13
            | exact resolve b4e13 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e105 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b4e26
          have b4e111 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e105 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e105
            | exact resolve b4e105 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105
          have b4e112 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b4e111
          have b4e276 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e41 X0 X1 y
               have i₂ := b4e43 X0
               grind)
            | exact superpose b4e43 b4e41
            | exact resolve b4e41 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e43
          have b4e351 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e276 X0 (σ y)
               have i₂ := b4e44 X0
               grind)
            | exact superpose b4e44 b4e276
            | exact resolve b4e276 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e276
          have b4e432 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e351 (σ x)
               grind)
            | exact superpose b4e351 b4e20
            | exact resolve b4e20 b4e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2071 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b4e30 (M.op (τ X0) (τ X0))
               have i₂ := b4e112 X0
               grind)
            | exact superpose b4e112 b4e30
            | exact resolve b4e30 b4e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e112
          have b4e2077 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e2071 X0
               have i₂ := b4e58 (τ X0) (M.op (τ X0) (τ X0))
               grind)
            | exact superpose b4e58 b4e2071
            | exact resolve b4e2071 b4e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2071
          have b4e2080 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e2077 X0
               have i₂ := b4e351 (τ X0)
               grind)
            | exact superpose b4e351 b4e2077
            | exact resolve b4e2077 b4e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2077
          have b4e2081 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e2080 X0
               have i₂ := b4e58 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e58 b4e2080
            | exact resolve b4e2080 b4e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58 b4e2080
          have b4e2082 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e2081 X0
               have i₂ := b4e351 X0
               grind)
            | exact superpose b4e351 b4e2081
            | exact resolve b4e2081 b4e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e351 b4e2081
          have b4e2619 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e2082 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e2082
            | exact resolve b4e2082 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2082
          have b4e2896 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e432
               have i₂ := b4e2619 x
               grind)
            | exact superpose b4e2619 b4e432
            | (have r₁ := b4e432
               have r₂ := b4e2619 x
               grind)
            | exact resolve b4e432 b4e2619
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e432 b4e2619
          have b4e2903 : False := by grind
          exact b4e2903
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e116 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e121 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e116
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e116
            | exact resolve b5e116 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116
          have b5e122 : False := by grind
          exact b5e122
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e32 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) (σ y) x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e32 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e90 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e41 (σ y)
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e41
            | exact resolve b7e41 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e41
          have b7e98 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e14
            | exact resolve b7e14 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e99 : y = (M.op y y) := by
            first
            | (have i₁ := b7e98
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e98
            | exact resolve b7e98 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e103 : False := by grind
          exact b7e103
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (M.op (σ X1) (σ X1)) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e61 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e61
            | (have j0 := b8e61 X0 X1
               grind)
            | exact resolve b8e61 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e76 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e1559 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e70 x y
               grind)
            | exact superpose b8e70 b8e20
            | (have j1 := b8e70 (M.op y y) y
               grind)
            | exact resolve b8e20 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
          have b8e1594 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e1559
               have r₂ := b8e76
               grind)
            | exact resolve b8e1559 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76 b8e1559
          have b8e1607 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1594
               have r₂ := b8e23
               grind)
            | exact resolve b8e1594 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1594
          have b8e1625 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e1607
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1607
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | (have r₁ := b8e1607
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1607
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1607 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1607
          have b8e1626 : y = (M.op y y) ∨ x = y := by grind
          clear b8e1625
          have b8e1629 : x = y := by
            first
            | (have r₁ := b8e1626
               have r₂ := b8e22
               grind)
            | exact resolve b8e1626 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1626
          have b8e1633 : False := by grind
          exact b8e1633

/-- `Equation4437`: `x ◇ (y ◇ x) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then Y else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_x_y_y_pxy_Equation4437 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e38 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
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
      have b0e39 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
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
      have b0e42 : ∀ X0 : G, x = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e39 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e39
        | exact resolve b0e39 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e43 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e38 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e38
        | exact resolve b0e38 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e77 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e43 (σ y)
           grind)
        | exact superpose b0e43 b0e18
        | exact resolve b0e18 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e86 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e77
           have i₂ := b0e42 y
           grind)
        | exact superpose b0e42 b0e77
        | exact resolve b0e77 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e77
      have b0e87 : False := by grind
      exact b0e87
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : ∀ X0 : G, x ≠ x ∨ (k x X0) = X0 := by
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
        have b1e26 : ∀ X0 : G, (k x X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e37 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ y) (σ y) x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
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
        have b1e41 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e38 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e38
          | exact resolve b1e38 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e67 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 X1 X2
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e12 X0 X1 X2
             have i₂ := b1e17 (M.op X1 X0) X1
             grind)
          | exact superpose b1e17 b1e12
          | (have j1 := b1e17 X0 X0
             grind)
          | exact resolve b1e12 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b1e139 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e28 X0 x
             have i₂ := b1e26 (τ X0)
             grind)
          | exact superpose b1e26 b1e28
          | exact resolve b1e28 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e147 : ∀ X0 : G, (k (σ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e139 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e139
          | exact resolve b1e139 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e139
        have b1e158 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e37 X1
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e37
          | exact resolve b1e37 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e2165 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e19
             have i₂ := b1e67 (σ x) X0 (σ y)
             grind)
          | (have i₁ := b1e19
             have i₂ := b1e67 (σ y) (σ x) x
             grind)
          | exact superpose b1e67 b1e19
          | (have j1 := b1e67 (σ x) X0 x
             grind)
          | exact resolve b1e19 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2260 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b1e2165 X0
             grind)
          | (have r₁ := b1e2165 X0
             have r₂ := b1e21
             grind)
          | exact resolve b1e2165 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2165
        have b1e2313 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e2260 X0
             have i₂ := b1e41 y
             grind)
          | exact superpose b1e41 b1e2260
          | (have j0 := b1e2260 X0
             grind)
          | exact resolve b1e2260 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e2260
        have b1e2325 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e2313 X0
             have i₂ := b1e147 X0
             grind)
          | exact superpose b1e147 b1e2313
          | (have j0 := b1e2313 X0
             grind)
          | exact resolve b1e2313 b1e147
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2313
        have b1e3022 : ∀ X0 X1 : G, (σ (k x X0)) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e158 X1 (σ X0)
             have i₂ := b1e72 x X0
             grind)
          | exact superpose b1e72 b1e158
          | (have j1 := b1e72 x x
             grind)
          | exact resolve b1e158 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72 b1e158
        have b1e3238 : ∀ X0 X1 : G, (σ (k x X0)) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e3022 X0 X1
             grind)
          | (have r₁ := b1e3022 X0 X1
             have r₂ := b1e21
             grind)
          | (have r₁ := b1e3022 x X1
             have r₂ := b1e21
             grind)
          | exact resolve b1e3022 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3022
        have b1e3281 : ∀ X0 X1 : G, (σ X0) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e3238 X0 X1
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e3238
          | (have j0 := b1e3238 X0 X1
             grind)
          | exact resolve b1e3238 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e3238
        have b1e7373 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) X1) = (k (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e2325 X1
             have i₂ := b1e67 (σ x) X1 X0
             grind)
          | (have i₁ := b1e2325 X0
             have i₂ := b1e67 X0 X1 (σ x)
             grind)
          | exact superpose b1e67 b1e2325
          | (have j0 := b1e2325 X1
             have j1 := b1e67 (σ x) X1 x
             grind)
          | (have r₁ := b1e2325 (σ x)
             have r₂ := b1e67 (σ x) X1 x
             grind)
          | exact resolve b1e2325 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67 b1e2325
        have b1e7404 : ∀ X1 : G, (M.op (σ x) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) X1) = (k (σ x) X1) := by
          intro X1
          first
          | (have j0 := b1e7373 x X1
             have j1 := b1e3281 x (σ x)
             grind)
          | (have r₁ := b1e7373 X1 X1
             have r₂ := b1e3281 x X1
             grind)
          | (have r₁ := b1e7373 (σ x) X1
             have r₂ := b1e3281 x X1
             grind)
          | exact resolve b1e7373 b1e3281
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3281 b1e7373
        have b1e7416 : ∀ X1 : G, (M.op (σ x) X1) = X1 ∨ (M.op (σ x) X1) = (k (σ x) X1) := by
          intro X1
          first
          | (have j0 := b1e7404 X1
             grind)
          | (have r₁ := b1e7404 (σ x)
             have r₂ := b1e21
             grind)
          | (have r₁ := b1e7404 X1
             have r₂ := b1e21
             grind)
          | exact resolve b1e7404 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7404
        have b1e7417 : ∀ X1 : G, (M.op (σ x) X1) = X1 ∨ (M.op (σ x) X1) = X1 := by
          intro X1
          first
          | (have i₁ := b1e7416 X1
             have i₂ := b1e147 X1
             grind)
          | exact superpose b1e147 b1e7416
          | (have j0 := b1e7416 X1
             grind)
          | exact resolve b1e7416 b1e147
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e147 b1e7416
        have b1e7418 : ∀ X1 : G, (M.op (σ x) X1) = X1 := by
          intro X1
          first
          | (have j0 := b1e7417 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7417
        have b1e7440 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e7418 (σ x)
             grind)
          | exact superpose b1e7418 b1e21
          | (have r₁ := b1e21
             have r₂ := b1e7418 (σ x)
             grind)
          | exact resolve b1e21 b1e7418
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7418
        have b1e7529 : False := by grind
        exact b1e7529
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 : G, x ≠ x ∨ (k x X0) = X0 := by
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
        have b2e25 : ∀ X0 : G, (k x X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
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
        have b2e33 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
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
        have b2e39 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e33 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e33
          | exact resolve b2e33 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e58 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X1 X2
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e17 (M.op X1 X0) X1
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X0 X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e68 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e58 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e129 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e27 X0 x
             have i₂ := b2e25 (τ X0)
             grind)
          | exact superpose b2e25 b2e27
          | exact resolve b2e27 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e27
        have b2e137 : ∀ X0 : G, (k (σ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e129 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e129
          | exact resolve b2e129 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e129
        have b2e1073 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ x) ∨ (M.op (σ x) (M.op X0 X1)) = (k (σ x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 (M.op X0 X1)
             have i₂ := b2e68 (M.op X0 X1)
             grind)
          | exact superpose b2e68 b2e12
          | (have j1 := b2e68 (M.op X0 X1)
             grind)
          | exact resolve b2e12 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1087 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ x) (M.op X0 X1)) ∨ (M.op X0 (M.op X1 X0)) = (σ x) := by
          intro X0 X1
          first
          | (have i₁ := b2e1073 X0 X1
             have i₂ := b2e137 (M.op X0 X1)
             grind)
          | exact superpose b2e137 b2e1073
          | (have j0 := b2e1073 X0 X1
             grind)
          | exact resolve b2e1073 b2e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1073
        have b2e1810 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e19
             have i₂ := b2e62 (σ x) X0 (σ y)
             grind)
          | (have i₁ := b2e19
             have i₂ := b2e62 (σ y) (σ x) x
             grind)
          | exact superpose b2e62 b2e19
          | (have j1 := b2e62 (σ x) X0 x
             grind)
          | exact resolve b2e19 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e1881 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e1810 X0
             grind)
          | (have r₁ := b2e1810 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e1810 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1810
        have b2e1926 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e1881 X0
             have i₂ := b2e39 y
             grind)
          | exact superpose b2e39 b2e1881
          | (have j0 := b2e1881 X0
             grind)
          | exact resolve b2e1881 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e1881
        have b2e1938 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1926 X0
             have i₂ := b2e137 X0
             grind)
          | exact superpose b2e137 b2e1926
          | (have j0 := b2e1926 X0
             grind)
          | exact resolve b2e1926 b2e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1926
        have b2e6216 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (σ x) ∨ (M.op X0 X1) = (M.op (σ x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e1938 (M.op X0 X1)
             have i₂ := b2e12 X0 X1 (σ x)
             grind)
          | exact superpose b2e12 b2e1938
          | (have j0 := b2e1938 (M.op X0 X1)
             grind)
          | exact resolve b2e1938 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1938
        have b2e6234 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e6216 X0 X1
             have j1 := b2e1087 X0 X1
             grind)
          | (have r₁ := b2e6216 X0 X1
             have r₂ := b2e1087 X0 X1
             grind)
          | exact resolve b2e6216 b2e1087
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1087 b2e6216
        have b2e6439 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e6234 X0 X0
             have i₂ := b2e68 X0
             grind)
          | exact superpose b2e68 b2e6234
          | (have j1 := b2e68 (σ x)
             grind)
          | exact resolve b2e6234 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68 b2e6234
        have b2e6555 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e6439 X0
             grind)
          | (have r₁ := b2e6439 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e6439 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6439
        have b2e6564 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e6555 X0
             have i₂ := b2e137 X0
             grind)
          | exact superpose b2e137 b2e6555
          | exact resolve b2e6555 b2e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e137 b2e6555
        have b2e6926 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e6564 (σ x)
             grind)
          | exact superpose b2e6564 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e6564 (σ x)
             grind)
          | exact resolve b2e21 b2e6564
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6564
        have b2e7005 : False := by grind
        exact b2e7005
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = X0 := by
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
        have b3e26 : ∀ X0 : G, (k (σ x) X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e25 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e18
          | exact resolve b3e18 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 : G, (σ X0) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b3e26 (σ X0)
             have i₂ := b3e18 x X0
             grind)
          | exact superpose b3e18 b3e26
          | exact resolve b3e26 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e33 : ∀ X0 : G, (τ (σ X0)) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e13 (k x X0)
             have i₂ := b3e30 X0
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e34 : ∀ X0 : G, (k x X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e33 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e33
          | exact resolve b3e33 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X0 X1 X3
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X0 (M.op X1 X0) X3
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 (M.op X0 X1) X2 X3
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
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
        have b3e46 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e12 y y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e45 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e45
          | exact resolve b3e45 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e50 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e44 X0 X1 x X3
             have i₂ := b3e12 X0 X1 (M.op x (M.op X0 X1))
             grind)
          | exact superpose b3e12 b3e44
          | exact resolve b3e44 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e53 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e46 X1
             have i₂ := b3e46 X0
             grind)
          | exact superpose b3e46 b3e46
          | exact resolve b3e46 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e73 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X2 X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X0 X1 (M.op X0 X1)
             have i₂ := b3e17 (M.op X0 X1) X2
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 (M.op X0 X1) X2
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e76 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X1 X2
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 (M.op X1 X0) X1
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e93 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (σ x) X1
             have i₂ := b3e49 X0
             grind)
          | exact superpose b3e49 b3e12
          | exact resolve b3e12 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e99 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e114 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e99 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e99
        have b3e119 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e114 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e114 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e114 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e114
        have b3e140 : ∀ X0 : G, x ≠ (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e20
             have i₂ := b3e53 x X0
             grind)
          | (have i₁ := b3e20
             have i₂ := b3e53 X0 x
             grind)
          | exact superpose b3e53 b3e20
          | exact resolve b3e20 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e157 : x ≠ (M.op y x) := by
          first
          | (have i₁ := b3e140 x
             have i₂ := b3e46 x
             grind)
          | exact superpose b3e46 b3e140
          | exact resolve b3e140 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e140
        have b3e169 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e28 X1 X0
             grind)
          | exact superpose b3e28 b3e13
          | exact resolve b3e13 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e225 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X3) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e12 (M.op X0 X1) X3 X4
             have i₂ := b3e41 X0 X1 (M.op X3 (M.op X0 X1)) X2
             grind)
          | (have i₁ := b3e12 (M.op X0 X1) X3 X4
             have i₂ := b3e41 X0 X1 X2 (M.op X3 (M.op X0 X1))
             grind)
          | exact superpose b3e41 b3e12
          | exact resolve b3e12 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e238 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e119 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e119
        have b3e1550 : ∀ X0 : G, (M.op y x) = (M.op X0 x) ∨ x = (M.op x x) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e46 x
             have i₂ := b3e76 x X0 x
             grind)
          | (have i₁ := b3e46 X0
             have i₂ := b3e76 X0 x x
             grind)
          | exact superpose b3e76 b3e46
          | (have j1 := b3e76 x X0 x
             grind)
          | exact resolve b3e46 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76
        have b3e1620 : ∀ X0 : G, (M.op y x) = (M.op X0 x) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b3e1550 X0
             grind)
          | (have r₁ := b3e1550 X0
             have r₂ := b3e20
             grind)
          | exact resolve b3e1550 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1550
        have b3e1656 : ∀ X0 : G, (M.op x X0) = X0 ∨ (M.op y x) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e1620 X0
             have i₂ := b3e34 X0
             grind)
          | exact superpose b3e34 b3e1620
          | (have j0 := b3e1620 X0
             grind)
          | exact resolve b3e1620 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e1620
        have b3e4806 : ∀ X0 : G, (M.op y x) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (M.op x (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e93 X0 x
             have i₂ := b3e1656 (M.op X0 (σ x))
             grind)
          | exact superpose b3e1656 b3e93
          | (have j1 := b3e1656 (M.op X0 (σ x))
             grind)
          | exact resolve b3e93 b3e1656
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e93
        have b3e4813 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ (M.op X0 (M.op X1 X0)) = (M.op x (M.op X0 (M.op X1 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e50 X0 X1 x
             have i₂ := b3e1656 (M.op X0 (M.op X1 X0))
             grind)
          | exact superpose b3e1656 b3e50
          | (have j1 := b3e1656 (M.op X0 (M.op X1 X0))
             grind)
          | exact resolve b3e50 b3e1656
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e4817 : (σ x) = (M.op y x) ∨ (σ x) = (M.op x (σ x)) := by
          first
          | (have i₁ := b3e49 x
             have i₂ := b3e1656 (σ x)
             grind)
          | exact superpose b3e1656 b3e49
          | (have j1 := b3e1656 (σ x)
             grind)
          | exact resolve b3e49 b3e1656
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49 b3e1656
        have b3e4819 : (σ x) = (M.op y x) ∨ (σ x) = (M.op y x) := by
          first
          | (have i₁ := b3e4817
             have i₂ := b3e46 (σ x)
             grind)
          | exact superpose b3e46 b3e4817
          | exact resolve b3e4817 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4817
        have b3e4820 : (σ x) = (M.op y x) := by grind
        clear b3e4819
        have b3e4824 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ (M.op X0 (M.op X1 X0)) = (M.op y x) := by
          intro X0 X1
          first
          | (have i₁ := b3e4813 X0 X1
             have i₂ := b3e46 (M.op X0 (M.op X1 X0))
             grind)
          | exact superpose b3e46 b3e4813
          | (have j0 := b3e4813 X0 X1
             grind)
          | exact resolve b3e4813 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4813
        have b3e4825 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) := by
          intro X0 X1
          first
          | (have j0 := b3e4824 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4824
        have b3e4831 : ∀ X0 : G, (M.op y x) = (M.op X0 (σ x)) ∨ (M.op y x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e4806 X0
             have i₂ := b3e46 (M.op X0 (σ x))
             grind)
          | exact superpose b3e46 b3e4806
          | (have j0 := b3e4806 X0
             grind)
          | exact resolve b3e4806 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4806
        have b3e4832 : ∀ X0 : G, (M.op y x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b3e4831 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4831
        have b3e4881 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ x) := by
          intro X0 X1
          first
          | (have i₁ := b3e4825 X0 X1
             have i₂ := b3e4820
             grind)
          | exact superpose b3e4820 b3e4825
          | exact resolve b3e4825 b3e4820
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4825
        have b3e4887 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e4832 X0
             have i₂ := b3e4820
             grind)
          | exact superpose b3e4820 b3e4832
          | exact resolve b3e4832 b3e4820
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4832
        have b3e4984 : ∀ X0 : G, (σ x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e46 X0
             have i₂ := b3e4820
             grind)
          | exact superpose b3e4820 b3e46
          | exact resolve b3e46 b3e4820
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e4985 : x ≠ (σ x) := by
          first
          | (have i₁ := b3e157
             have i₂ := b3e4820
             grind)
          | exact superpose b3e4820 b3e157
          | exact resolve b3e157 b3e4820
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e157 b3e4820
        have b3e5737 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e43 X0 X1 x x
             have i₂ := b3e225 X0 X1 X2 x x
             grind)
          | exact superpose b3e225 b3e43
          | exact resolve b3e43 b3e225
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e225
        have b3e5831 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (σ x) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e5737 X0 X1 X2
             have i₂ := b3e4881 X0 (M.op X1 X0)
             grind)
          | exact superpose b3e4881 b3e5737
          | exact resolve b3e5737 b3e4881
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5737
        have b3e5963 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e238 X0 (σ x)
             have i₂ := b3e4887 X0
             grind)
          | exact superpose b3e4887 b3e238
          | (have j0 := b3e238 X0 (σ x)
             grind)
          | (have r₁ := b3e238 X0 (σ x)
             have r₂ := b3e4887 X0
             grind)
          | exact resolve b3e238 b3e4887
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e238 b3e4887
        have b3e5996 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b3e5963 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5963
        have b3e6276 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e169 X0 (σ x)
             have i₂ := b3e5996 (σ X0)
             grind)
          | exact superpose b3e5996 b3e169
          | exact resolve b3e169 b3e5996
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e169 b3e5996
        have b3e6278 : ∀ X0 : G, x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b3e6276 X0
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e6276
          | exact resolve b3e6276 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6276
        have b3e6539 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) x) ∨ (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op x x) := by
          intro X0 X1
          first
          | (have i₁ := b3e73 X0 X1 x
             have i₂ := b3e6278 (M.op X0 X1)
             grind)
          | exact superpose b3e6278 b3e73
          | (have j0 := b3e73 X0 X1 x
             grind)
          | exact resolve b3e73 b3e6278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73 b3e6278
        have b3e6542 : ∀ X0 X1 : G, x = (σ x) ∨ (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op x x) := by
          intro X0 X1
          first
          | (have i₁ := b3e6539 X0 X1
             have i₂ := b3e5831 X0 X1 x
             grind)
          | exact superpose b3e5831 b3e6539
          | (have j0 := b3e6539 X0 X1
             grind)
          | exact resolve b3e6539 b3e5831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5831 b3e6539
        have b3e6560 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op x x) := by
          intro X0 X1
          first
          | (have j0 := b3e6542 X0 X1
             grind)
          | (have r₁ := b3e6542 X0 X1
             have r₂ := b3e4985
             grind)
          | exact resolve b3e6542 b3e4985
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6542
        have b3e6562 : ∀ X0 X1 : G, (M.op X0 X1) = (σ x) ∨ (M.op X0 X1) = (M.op x x) := by
          intro X0 X1
          first
          | (have i₁ := b3e6560 X0 X1
             have i₂ := b3e4881 X0 X1
             grind)
          | exact superpose b3e4881 b3e6560
          | (have j0 := b3e6560 X0 X1
             grind)
          | exact resolve b3e6560 b3e4881
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4881 b3e6560
        have b3e6564 : ∀ X0 X1 : G, (M.op X0 X1) = (σ x) ∨ (M.op X0 X1) = (σ x) := by
          intro X0 X1
          first
          | (have i₁ := b3e6562 X0 X1
             have i₂ := b3e4984 x
             grind)
          | exact superpose b3e4984 b3e6562
          | (have j0 := b3e6562 X0 X1
             grind)
          | exact resolve b3e6562 b3e4984
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4984 b3e6562
        have b3e6565 : ∀ X0 X1 : G, (M.op X0 X1) = (σ x) := by
          intro X0 X1
          first
          | (have j0 := b3e6564 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6564
        have b3e6867 : x = (σ x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e6565 y y
             grind)
          | exact superpose b3e6565 b3e21
          | exact resolve b3e21 b3e6565
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6565
        have b3e6870 : False := by grind
        exact b3e6870
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op x x) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e42 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) (σ y) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e13 y y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e48 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e43 X1
               have i₂ := b4e43 X0
               grind)
            | exact superpose b4e43 b4e43
            | exact resolve b4e43 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e68 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e23
               have i₂ := b4e18 (σ x) X0
               grind)
            | exact superpose b4e18 b4e23
            | (have j1 := b4e18 (σ x) X0
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e18 (σ x) x
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e18 (σ x) (σ x)
               grind)
            | exact resolve b4e23 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e78 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e68 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e151 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e42 X1
               have i₂ := b4e42 X0
               grind)
            | exact superpose b4e42 b4e42
            | exact resolve b4e42 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e255 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e23
               have i₂ := b4e151 (σ x) X0
               grind)
            | (have i₁ := b4e23
               have i₂ := b4e151 X0 (σ x)
               grind)
            | exact superpose b4e151 b4e23
            | exact resolve b4e23 b4e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e256 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e20
               have i₂ := b4e151 (σ y) X0
               grind)
            | (have i₁ := b4e20
               have i₂ := b4e151 X0 (σ y)
               grind)
            | exact superpose b4e151 b4e20
            | exact resolve b4e20 b4e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1096 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e78 (σ X0)
               grind)
            | exact superpose b4e78 b4e19
            | (have j1 := b4e78 (σ X0)
               grind)
            | exact resolve b4e19 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e1684 : ∀ X0 X1 : G, (M.op (σ x) X1) ≠ (σ (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e256 X1
               have i₂ := b4e48 y X0
               grind)
            | (have i₁ := b4e256 X1
               have i₂ := b4e48 X0 y
               grind)
            | exact superpose b4e48 b4e256
            | exact resolve b4e256 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48 b4e256
          have b4e51695 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (σ (k x x)) := by
            intro X0
            first
            | (have i₁ := b4e1096 x
               have i₂ := b4e151 (σ x) x
               grind)
            | (have i₁ := b4e1096 x
               have i₂ := b4e151 X0 (σ x)
               grind)
            | exact superpose b4e151 b4e1096
            | exact resolve b4e1096 b4e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e151 b4e1096
          have b4e52052 : ∀ X0 : G, (M.op (σ x) X0) = (σ (k x x)) := by
            intro X0
            first
            | (have j0 := b4e51695 X0
               grind)
            | (have r₁ := b4e51695 X0
               have r₂ := b4e255 X0
               grind)
            | exact resolve b4e51695 b4e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e255 b4e51695
          have b4e52548 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b4e52052 X0
               have i₂ := b4e18 x x
               grind)
            | exact superpose b4e18 b4e52052
            | (have j1 := b4e18 x x
               grind)
            | exact resolve b4e52052 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52052
          have b4e52802 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x x)) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have j0 := b4e52548 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52548
          have b4e52908 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x x)) := by
            intro X0
            first
            | (have j0 := b4e52802 X0
               grind)
            | (have r₁ := b4e52802 X0
               have r₂ := b4e21
               grind)
            | exact resolve b4e52802 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52802
          have b4e52942 : False := by grind
          exact b4e52942
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 : G, x ≠ y ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e16 y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y X0
               grind)
            | exact resolve b5e16 b5e22
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
          have b5e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e14
            | exact resolve b5e14 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e38 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e13 y y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X0 X1) X2 X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 (M.op X2 (M.op X0 X1))
               have i₂ := b5e13 (M.op X0 X1) X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e40 X0 X1 x X3
               have i₂ := b5e13 X0 X1 (M.op x (M.op X0 X1))
               grind)
            | exact superpose b5e13 b5e40
            | exact resolve b5e40 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e45 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e38 X1
               have i₂ := b5e38 X0
               grind)
            | exact superpose b5e38 b5e38
            | exact resolve b5e38 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e67 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X1 X2
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 (M.op X1 X0) X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e70 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b5e86 : ∀ X0 : G, x ≠ (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e21
               have i₂ := b5e45 x X0
               grind)
            | (have i₁ := b5e21
               have i₂ := b5e45 X0 x
               grind)
            | exact superpose b5e45 b5e21
            | exact resolve b5e21 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e99 : x = (M.op x x) ∨ y = (k x y) := by grind
          have b5e113 : y = (k x y) := by
            first
            | (have r₁ := b5e99
               have r₂ := b5e21
               grind)
            | exact resolve b5e99 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99
          have b5e267 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X0 X1) X2) ∨ (k (M.op (M.op X0 X1) X2) X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e16 (M.op (M.op X0 X1) X2) X3
               have i₂ := b5e41 X0 X1 X2 (M.op (M.op X0 X1) X2)
               grind)
            | exact superpose b5e41 b5e16
            | (have j0 := b5e16 (M.op (M.op X0 X1) X2) X3
               grind)
            | exact resolve b5e16 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e273 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X0 X1) X2) X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b5e267 X0 X1 X2 X3
               grind)
            | (have r₁ := b5e267 X0 X1 X2 X3
               have r₂ := b5e13 X0 X1 X2
               grind)
            | exact resolve b5e267 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e267
          have b5e1198 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e70 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70
          have b5e1199 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1198
               have r₂ := b5e23
               grind)
            | exact resolve b5e1198 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1198
          have b5e1200 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1199
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1199
            | exact resolve b5e1199 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1199
          have b5e1201 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1200
               have i₂ := b5e113
               grind)
            | exact superpose b5e113 b5e1200
            | exact resolve b5e1200 b5e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113 b5e1200
          have b5e1213 : ∀ X0 X1 : G, (k (M.op (σ y) X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e273 (σ x) (σ y) X0 X1
               have i₂ := b5e1201
               grind)
            | exact superpose b5e1201 b5e273
            | exact resolve b5e273 b5e1201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e273
          have b5e1458 : ∀ X0 : G, x = (k y y) ∨ x = (M.op y X0) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b5e67 y y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e67
            | exact resolve b5e67 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67
          have b5e2439 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e71 y y
               grind)
            | exact superpose b5e71 b5e24
            | (have j1 := b5e71 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e71 x y
               grind)
            | exact resolve b5e24 b5e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e2579 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e2439
          have b5e3875 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ y) X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 (M.op (σ y) X1) X0
               have i₂ := b5e1213 X1 (σ X0)
               grind)
            | exact superpose b5e1213 b5e32
            | exact resolve b5e32 b5e1213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e1213
          have b5e3902 : ∀ X0 X1 : G, (k (τ (M.op (σ y) X1)) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e3875 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e3875
            | exact resolve b5e3875 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3875
          have b5e6016 : ∀ X1 : G, x = (M.op x X1) ∨ x = (k y y) ∨ x = y := by
            intro X1
            first
            | (have i₁ := b5e43 y X1 x
               have i₂ := b5e1458 (M.op X1 y)
               grind)
            | exact superpose b5e1458 b5e43
            | exact resolve b5e43 b5e1458
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e1458
          have b5e6033 : x = (k y y) ∨ x = y := by
            first
            | (have r₁ := b5e6016 x
               have r₂ := b5e86 x
               grind)
            | exact resolve b5e6016 b5e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86 b5e6016
          have b5e13398 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e2579
               have i₂ := b5e6033
               grind)
            | exact superpose b5e6033 b5e2579
            | exact resolve b5e2579 b5e6033
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2579
          have b5e13412 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
          clear b5e13398
          have b5e73973 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 ∨ x = y := by
            intro X0
            first
            | (have i₁ := b5e3902 X0 (σ y)
               have i₂ := b5e13412
               grind)
            | exact superpose b5e13412 b5e3902
            | exact resolve b5e3902 b5e13412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3902 b5e13412
          have b5e74124 : ∀ X0 : G, (k y X0) = X0 ∨ x = y := by
            intro X0
            first
            | (have i₁ := b5e73973 X0
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e73973
            | exact resolve b5e73973 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73973
          have b5e74129 : ∀ X0 : G, (k y X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e74124 X0
               have j1 := b5e26 X0
               grind)
            | (have r₁ := b5e74124 X0
               have r₂ := b5e26 X0
               grind)
            | exact resolve b5e74124 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e74124
          have b5e75790 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e6033
               have i₂ := b5e74129 y
               grind)
            | exact superpose b5e74129 b5e6033
            | exact resolve b5e6033 b5e74129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6033 b5e74129
          have b5e75819 : x = y := by grind
          clear b5e75790
          have b5e77528 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e1201
               have i₂ := b5e75819
               grind)
            | exact superpose b5e75819 b5e1201
            | exact resolve b5e1201 b5e75819
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1201 b5e75819
          have b5e77585 : False := by grind
          exact b5e77585
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = X0 := by
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
        have b6e25 : ∀ X0 : G, (k (σ x) X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e29 : ∀ X0 : G, (σ X0) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b6e25 (σ X0)
             have i₂ := b6e18 x X0
             grind)
          | exact superpose b6e18 b6e25
          | exact resolve b6e25 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e32 : ∀ X0 : G, (τ (σ X0)) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b6e13 (k x X0)
             have i₂ := b6e29 X0
             grind)
          | exact superpose b6e29 b6e13
          | exact resolve b6e13 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e33 : ∀ X0 : G, (k x X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e32
          | exact resolve b6e32 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e82 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x x) ∨ (M.op X0 X0) = x := by
          intro X0
          first
          | (have i₁ := b6e33 X0
             have i₂ := b6e17 x X0
             grind)
          | exact superpose b6e17 b6e33
          | (have j1 := b6e17 x x
             grind)
          | exact resolve b6e33 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e86 : ∀ X0 : G, (M.op x X0) = X0 ∨ (M.op X0 X0) = x := by
          intro X0
          first
          | (have j0 := b6e82 X0
             grind)
          | (have r₁ := b6e82 x
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e82 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e82 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e3878 : x ≠ x ∨ x = (M.op x x) := by
          first
          | (have j0 := b6e86 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e3879 : x = (M.op x x) := by grind
        clear b6e3878
        have b6e3886 : False := by grind
        exact b6e3886
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e16 (M.op X0 X1) X2
               have i₂ := b7e13 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b7e13 b7e16
            | (have j0 := b7e16 (M.op X0 X1) X2
               grind)
            | exact resolve b7e16 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 X2) = X2 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e16 X1 X2
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e16 X0 X1
               have i₂ := b7e18 (M.op X0 X0) X1
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X1 X2
               have j1 := b7e18 X0 X0
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X0
               grind)
            | (have r₁ := b7e16 (M.op X1 X1) X1
               have r₂ := b7e18 (M.op (M.op X1 X1) (M.op X1 X1)) X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e18 (σ X0) (σ X1)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X0) (σ X0)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e78 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          have b7e97 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e78
               have r₂ := b7e23
               grind)
            | exact resolve b7e78 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e98 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e97
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e97
            | exact resolve b7e97 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97
          have b7e110 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e98
               grind)
            | exact superpose b7e98 b7e14
            | exact resolve b7e14 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e111 : y = (k x y) := by
            first
            | (have i₁ := b7e110
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e110
            | exact resolve b7e110 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e117 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e111
               grind)
            | exact superpose b7e111 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
          have b7e118 : y = (M.op x y) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e117
               have r₂ := b7e21
               grind)
            | exact resolve b7e117 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e117
          have b7e120 : y = (M.op x y) := by
            first
            | (have r₁ := b7e118
               have r₂ := b7e22
               grind)
            | exact resolve b7e118 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118
          have b7e992 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X2) = X2 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e38 X1 X1 X2
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e38 X0 X1 X2
               have i₂ := b7e18 (M.op X1 X0) X1
               grind)
            | exact superpose b7e18 b7e38
            | (have j1 := b7e18 X0 X0
               grind)
            | (have r₁ := b7e38 X1 X1 X2
               have r₂ := b7e18 (M.op X1 (M.op X1 X1)) X1
               grind)
            | exact resolve b7e38 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e1035 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X2) = X2 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e992 X0 X1 X2
               have j1 := b7e16 X0 X2
               grind)
            | (have r₁ := b7e992 X0 X1 X2
               have r₂ := b7e16 X0 X1
               grind)
            | exact resolve b7e992 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e992
          have b7e1981 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e59 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e1982 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e1981 X0 X1
               have j1 := b7e1035 X0 X0 X1
               grind)
            | (have r₁ := b7e1981 X0 X1
               have r₂ := b7e1035 X0 X0 x
               grind)
            | exact resolve b7e1981 b7e1035
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1035 b7e1981
          have b7e2478 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e65 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e65
            | exact resolve b7e65 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e2711 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e2478
          have b7e5019 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e2711
               grind)
            | exact superpose b7e2711 b7e14
            | exact resolve b7e14 b7e2711
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2711
          have b7e5036 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e5019
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e5019
            | exact resolve b7e5019 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5019
          have b7e6725 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e1982 y y
               have i₂ := b7e5036
               grind)
            | exact superpose b7e5036 b7e1982
            | exact resolve b7e1982 b7e5036
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1982 b7e5036
          have b7e6728 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b7e6725
               have r₂ := b7e22
               grind)
            | exact resolve b7e6725 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6725
          have b7e7175 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e6728
               grind)
            | exact superpose b7e6728 b7e14
            | exact resolve b7e14 b7e6728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6728
          have b7e7192 : x = y ∨ x = y := by
            first
            | (have i₁ := b7e7175
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e7175
            | exact resolve b7e7175 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7175
          have b7e7193 : x = y := by grind
          clear b7e7192
          have b7e7280 : x = (M.op x x) := by
            first
            | (have i₁ := b7e120
               have i₂ := b7e7193
               grind)
            | exact superpose b7e7193 b7e120
            | exact resolve b7e120 b7e7193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e120 b7e7193
          have b7e7304 : False := by grind
          exact b7e7304
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e59 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1094 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e59 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e1095 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1094
               have r₂ := b8e23
               grind)
            | exact resolve b8e1094 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1094
          have b8e1096 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1095
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1095
            | exact resolve b8e1095 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1095
          have b8e1097 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1096
               grind)
            | exact superpose b8e1096 b8e20
            | exact resolve b8e20 b8e1096
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1096
          have b8e1329 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e1097
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1097
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e1097 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1097
          have b8e1330 : x = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e1329
          have b8e1334 : x = (M.op y y) := by
            first
            | (have r₁ := b8e1330
               have r₂ := b8e21
               grind)
            | exact resolve b8e1330 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1330
          have b8e1337 : False := by grind
          exact b8e1337

/-- `Equation4437`: `x ◇ (y ◇ x) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_pyx_pxy_Equation4437 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : y ≠ y ∨ x = (k x y) := by
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
        have b1e28 : x = (k x y) := by grind
        clear b1e26
        have b1e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X0 X1 X3
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (σ x))) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (k X0 (M.op X1 X0)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 X0 (M.op X1 X0)
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e15
          | (have j0 := b1e15 X0 (M.op X1 X0)
             grind)
          | (have r₁ := b1e15 (M.op X0 X1) (M.op X0 (M.op X1 X0))
             have r₂ := b1e12 X0 X1 (M.op X0 (M.op X1 X0))
             grind)
          | exact resolve b1e15 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e65 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b1e68 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b1e65
        have b1e69 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b1e68
             have r₂ := b1e23
             grind)
          | exact resolve b1e68 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e70 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e69
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e69
          | exact resolve b1e69 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69
        have b1e71 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e70
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e70
          | exact resolve b1e70 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e70
        have b1e99 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ y) (σ x) X0
             have i₂ := b1e71
             grind)
          | exact superpose b1e71 b1e12
          | exact resolve b1e12 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e105 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e99 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e99
          | exact resolve b1e99 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e99
        have b1e106 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e105 X0
             have i₂ := b1e71
             grind)
          | exact superpose b1e71 b1e105
          | exact resolve b1e105 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e105
        have b1e1011 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) ≠ (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (M.op (σ y) (σ x)) (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b1e45 (σ x) (M.op (σ y) (σ x)) X1
             have i₂ := b1e42 X0
             grind)
          | (have i₁ := b1e45 (σ x) X0 x
             have i₂ := b1e42 X0
             grind)
          | exact superpose b1e42 b1e45
          | (have j0 := b1e45 (σ x) (M.op (σ y) (σ x)) x
             grind)
          | exact resolve b1e45 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e45
        have b1e1039 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) ≠ (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (k (σ x) (M.op (M.op (σ y) (σ x)) (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b1e1011 X0 X1
             have i₂ := b1e12 (σ y) (σ x) (σ x)
             grind)
          | exact superpose b1e12 b1e1011
          | exact resolve b1e1011 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1011
        have b1e1054 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) ≠ (M.op (σ x) X1) ∨ (σ x) = (k (σ x) (M.op (M.op (σ y) (σ x)) (σ x))) := by
          intro X1
          first
          | (have i₁ := b1e1039 x X1
             have i₂ := b1e106 x
             grind)
          | exact superpose b1e106 b1e1039
          | exact resolve b1e1039 b1e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1039
        have b1e1062 : (σ x) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (M.op (σ y) (σ x)) (σ x))) := by
          first
          | (have i₁ := b1e1054 x
             have i₂ := b1e106 x
             grind)
          | exact superpose b1e106 b1e1054
          | exact resolve b1e1054 b1e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e106 b1e1054
        have b1e1068 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (M.op (M.op (σ y) (σ x)) (σ x))) := by
          first
          | (have i₁ := b1e1062
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e1062
          | exact resolve b1e1062 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1062
        have b1e1070 : (σ x) = (k (σ x) (M.op (M.op (σ y) (σ x)) (σ x))) := by
          first
          | (have r₁ := b1e1068
             have r₂ := b1e71
             grind)
          | exact resolve b1e1068 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1068
        have b1e1071 : (σ x) = (k (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
          first
          | (have i₁ := b1e1070
             have i₂ := b1e12 (σ y) (σ x) (σ x)
             grind)
          | exact superpose b1e12 b1e1070
          | exact resolve b1e1070 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1070
        have b1e1072 : (σ x) = (k (σ x) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b1e1071
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e1071
          | exact resolve b1e1071 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1071
        have b1e1073 : (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e1072
             have i₂ := b1e71
             grind)
          | exact superpose b1e71 b1e1072
          | exact resolve b1e1072 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71 b1e1072
        have b1e1074 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e1073
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e1073
          | exact resolve b1e1073 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1073
        have b1e1079 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e1074
             grind)
          | exact superpose b1e1074 b1e13
          | exact resolve b1e13 b1e1074
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1074
        have b1e1081 : x = (k x x) := by
          first
          | (have i₁ := b1e1079
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1079
          | exact resolve b1e1079 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1079
        have b1e1153 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e1081
             grind)
          | exact superpose b1e1081 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e1081
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1081
        have b1e1154 : x = (M.op x x) := by grind
        clear b1e1153
        have b1e1205 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e38 x x x x
             have i₂ := b1e1154
             grind)
          | exact superpose b1e1154 b1e38
          | exact resolve b1e38 b1e1154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e1359 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e1154
             have i₂ := b1e1205 x X0
             grind)
          | (have i₁ := b1e1154
             have i₂ := b1e1205 X0 x
             grind)
          | exact superpose b1e1205 b1e1154
          | exact resolve b1e1154 b1e1205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1154
        have b1e1360 : ∀ X0 : G, y = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e20
             have i₂ := b1e1205 y X0
             grind)
          | (have i₁ := b1e20
             have i₂ := b1e1205 X0 y
             grind)
          | exact superpose b1e1205 b1e20
          | exact resolve b1e20 b1e1205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1205
        have b1e1393 : x = y := by
          first
          | (have i₁ := b1e1359 x
             have i₂ := b1e1360 x
             grind)
          | exact superpose b1e1360 b1e1359
          | exact resolve b1e1359 b1e1360
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1359 b1e1360
        have b1e1627 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e1393
             grind)
          | exact superpose b1e1393 b1e23
          | exact resolve b1e23 b1e1393
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e1393
        have b1e1644 : False := by grind
        exact b1e1644
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b2e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e870 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e84 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e142747 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e870 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e870
          | (have j0 := b2e870 x y
             grind)
          | exact resolve b2e870 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e870
        have b2e142774 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e142747
        have b2e142796 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e142774
             have r₂ := b2e22
             grind)
          | exact resolve b2e142774 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e142774
        have b2e142806 : False := by grind
        exact b2e142806
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
        have b3e25 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e24
          | exact resolve b3e24 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e27 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b3e28 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b3e27
        have b3e29 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e28
          | exact resolve b3e28 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e34 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e29
             grind)
          | exact superpose b3e29 b3e13
          | exact resolve b3e13 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e35 : x = (k x y) := by
          first
          | (have i₁ := b3e34
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e34
          | exact resolve b3e34 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X0 X1 X3
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (σ x))) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) (σ y) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 : G, (M.op x (M.op y x)) = (M.op x X0) := by
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
        have b3e47 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X0 X1 (M.op X2 (M.op X0 X1))
             have i₂ := b3e12 (M.op X0 X1) X2 X3
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : x ≠ x ∨ x = y ∨ (k x y) = (M.op y x) := by
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
        have b3e55 : x = y ∨ (k x y) = (M.op y x) := by grind
        clear b3e54
        have b3e56 : (k x y) = (M.op y x) := by
          first
          | (have r₁ := b3e55
             have r₂ := b3e23
             grind)
          | exact resolve b3e55 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e55
        have b3e57 : x = (M.op y x) := by
          first
          | (have i₁ := b3e56
             have i₂ := b3e35
             grind)
          | exact superpose b3e35 b3e56
          | exact resolve b3e56 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35 b3e56
        have b3e58 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e12 y x X0
             have i₂ := b3e57
             grind)
          | exact superpose b3e57 b3e12
          | exact resolve b3e12 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e59 : x ≠ x ∨ y = (k y x) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e57
             grind)
          | exact superpose b3e57 b3e15
          | (have j0 := b3e15 y x
             grind)
          | (have r₁ := b3e15 y x
             have r₂ := b3e57
             grind)
          | exact resolve b3e15 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e60 : y = (k y x) := by grind
        clear b3e59
        have b3e61 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e58 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e58
          | exact resolve b3e58 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e62 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e61 X0
             have i₂ := b3e57
             grind)
          | exact superpose b3e57 b3e61
          | exact resolve b3e61 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57 b3e61
        have b3e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e83 : ∀ X0 : G, (M.op x (M.op y x)) ≠ X0 ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e15 x X0
             have i₂ := b3e46 X0
             grind)
          | (have i₁ := b3e15 x (M.op y x)
             have i₂ := b3e46 X0
             grind)
          | exact superpose b3e46 b3e15
          | (have j0 := b3e15 x X0
             grind)
          | (have r₁ := b3e15 x (M.op x (M.op y x))
             have r₂ := b3e46 (M.op x (M.op y x))
             grind)
          | exact resolve b3e15 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e84 : ∀ X0 : G, x ≠ X0 ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e83 X0
             have i₂ := b3e62 (M.op y x)
             grind)
          | exact superpose b3e62 b3e83
          | (have j0 := b3e83 X0
             grind)
          | (have r₁ := b3e83 x
             have r₂ := b3e62 (M.op y x)
             grind)
          | exact resolve b3e83 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62 b3e83
        have b3e113 : x = (k x x) := by
          first
          | (have j0 := b3e84 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e135 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e41 (σ x) (σ y) x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e41
          | exact resolve b3e41 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e156 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X3) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e12 (M.op X0 X1) X3 X4
             have i₂ := b3e41 X0 X1 (M.op X3 (M.op X0 X1)) X2
             grind)
          | (have i₁ := b3e12 (M.op X0 X1) X3 X4
             have i₂ := b3e41 X0 X1 X2 (M.op X3 (M.op X0 X1))
             grind)
          | exact superpose b3e41 b3e12
          | exact resolve b3e12 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e219 : ∀ X0 X1 : G, (M.op (σ y) X0) ≠ X1 ∨ (σ y) = (k (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 (σ y) X1
             have i₂ := b3e135 X1 X0
             grind)
          | (have i₁ := b3e15 (σ y) X1
             have i₂ := b3e135 X0 X1
             grind)
          | exact superpose b3e135 b3e15
          | (have j0 := b3e15 (σ y) X1
             grind)
          | (have r₁ := b3e15 (σ y) (M.op (σ y) X1)
             have r₂ := b3e135 (M.op (σ y) X1) X1
             grind)
          | (have r₁ := b3e15 (σ y) (M.op (σ y) X0)
             have r₂ := b3e135 X0 (M.op (σ y) X0)
             grind)
          | exact resolve b3e15 b3e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e223 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ x) (M.op (σ y) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e45 X1
             have i₂ := b3e135 (σ x) X0
             grind)
          | (have i₁ := b3e45 X1
             have i₂ := b3e135 X0 (σ x)
             grind)
          | exact superpose b3e135 b3e45
          | exact resolve b3e45 b3e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e135
        have b3e313 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (k X0 (M.op X1 X0)) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e15 X0 (M.op X1 X0)
             have i₂ := b3e47 X0 X1 X2 X3
             grind)
          | exact superpose b3e47 b3e15
          | (have j0 := b3e15 X0 (M.op X1 X0)
             grind)
          | (have r₁ := b3e15 (M.op (M.op X0 X1) X2) (M.op X0 (M.op X1 X0))
             have r₂ := b3e47 X0 X1 X2 (M.op X0 (M.op X1 X0))
             grind)
          | exact resolve b3e15 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e1096 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (σ (k y x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e45 X0
             have i₂ := b3e65 y x
             grind)
          | exact superpose b3e65 b3e45
          | (have j1 := b3e65 y x
             grind)
          | exact resolve b3e45 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e65 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e1125 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e1096 X0
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e1096
          | exact resolve b3e1096 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60 b3e1096
        have b3e1134 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e1125 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1125
          | exact resolve b3e1125 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1125
        have b3e1745 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (σ x) (M.op (σ y) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e223 x X0
             have i₂ := b3e45 x
             grind)
          | exact superpose b3e45 b3e223
          | exact resolve b3e223 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e223
        have b3e133116 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1117 x x
             have i₂ := b3e113
             grind)
          | exact superpose b3e113 b3e1117
          | (have j0 := b3e1117 x x
             grind)
          | exact resolve b3e1117 b3e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e113
        have b3e133141 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b3e133116
        have b3e133142 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b3e133141
        have b3e133217 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e41 (σ x) (σ x) x x
             have i₂ := b3e133142
             grind)
          | exact superpose b3e133142 b3e41
          | exact resolve b3e41 b3e133142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e133229 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e156 (σ x) (σ x) X2 x x
             have i₂ := b3e133142
             grind)
          | exact superpose b3e133142 b3e156
          | exact resolve b3e156 b3e133142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156
        have b3e134042 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e1745 X1
             have i₂ := b3e133217 (M.op (σ x) (M.op (σ y) (σ x))) X0
             grind)
          | (have i₁ := b3e1745 X1
             have i₂ := b3e133217 X0 (M.op (σ x) (M.op (σ y) (σ x)))
             grind)
          | exact superpose b3e133217 b3e1745
          | exact resolve b3e1745 b3e133217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1745
        have b3e134044 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e133142
             have i₂ := b3e133217 (σ x) X0
             grind)
          | (have i₁ := b3e133142
             have i₂ := b3e133217 X0 (σ x)
             grind)
          | exact superpose b3e133217 b3e133142
          | exact resolve b3e133142 b3e133217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e133142 b3e133217
        have b3e134460 : ∀ X1 : G, (σ x) = (M.op (σ y) X1) := by
          intro X1
          first
          | (have i₁ := b3e134042 x X1
             have i₂ := b3e134044 x
             grind)
          | exact superpose b3e134044 b3e134042
          | exact resolve b3e134042 b3e134044
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e134042 b3e134044
        have b3e135002 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) X2) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e313 (σ y) (σ x) X0 X1
             have i₂ := b3e1134 X2
             grind)
          | exact superpose b3e1134 b3e313
          | (have j0 := b3e313 (σ y) (σ x) X2 x
             have j1 := b3e1134 X2
             grind)
          | exact resolve b3e313 b3e1134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e313 b3e1134
        have b3e135486 : ∀ X2 : G, (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) X2) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          intro X2
          first
          | (have j0 := b3e135002 x x X2
             grind)
          | (have r₁ := b3e135002 x X2 X2
             have r₂ := b3e133229 (σ y) x X2
             grind)
          | exact resolve b3e135002 b3e133229
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e133229 b3e135002
        have b3e135576 : ∀ X2 : G, (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) X2) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          intro X2
          first
          | (have i₁ := b3e135486 X2
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e135486
          | (have j0 := b3e135486 X2
             grind)
          | exact resolve b3e135486 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e135486
        have b3e135615 : ∀ X2 : G, (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) X2) := by
          intro X2
          first
          | (have j0 := b3e135576 X2
             have j1 := b3e219 x (σ y)
             grind)
          | (have r₁ := b3e135576 x
             have r₂ := b3e219 x (σ y)
             grind)
          | (have r₁ := b3e135576 X2
             have r₂ := b3e219 (σ x) (σ y)
             grind)
          | exact resolve b3e135576 b3e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e135576
        have b3e135624 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have j1 := b3e219 x (σ y)
             grind)
          | (have r₁ := b3e135615 x
             have r₂ := b3e219 x (σ y)
             grind)
          | exact resolve b3e135615 b3e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e219 b3e135615
        have b3e135632 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e135624
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e135624
          | exact resolve b3e135624 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e135624
        have b3e135638 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e1117 y y
             have i₂ := b3e135632
             grind)
          | exact superpose b3e135632 b3e1117
          | (have j0 := b3e1117 y y
             grind)
          | (have r₁ := b3e1117 y y
             have r₂ := b3e135632
             grind)
          | exact resolve b3e1117 b3e135632
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1117 b3e135632
        have b3e135659 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b3e135638
        have b3e135660 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b3e135659
        have b3e135683 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e135660
             have i₂ := b3e134460 (σ y)
             grind)
          | exact superpose b3e134460 b3e135660
          | exact resolve b3e135660 b3e134460
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e134460 b3e135660
        have b3e135687 : False := by grind
        exact b3e135687
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (σ x) ≠ (σ x) := by
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
          have b4e29 : False := by grind
          exact b4e29
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 : G, (M.op x (M.op y x)) = (M.op x X0) := by
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
          have b5e46 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e38 X1
               have i₂ := b5e38 X0
               grind)
            | (have i₁ := b5e38 X0
               have i₂ := b5e38 (M.op y x)
               grind)
            | exact superpose b5e38 b5e38
            | exact resolve b5e38 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e88 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e46 y X0
               grind)
            | (have i₁ := b5e22
               have i₂ := b5e46 X0 y
               grind)
            | exact superpose b5e46 b5e22
            | exact resolve b5e22 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e117 : ∀ X0 : G, x ≠ X0 ∨ x = (k x X0) := by
            intro X0
            first
            | (have i₁ := b5e16 x X0
               have i₂ := b5e88 X0
               grind)
            | exact superpose b5e88 b5e16
            | (have j0 := b5e16 x X0
               grind)
            | (have r₁ := b5e16 x x
               have r₂ := b5e88 x
               grind)
            | exact resolve b5e16 b5e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88
          have b5e149 : x = (k x x) := by
            first
            | (have j0 := b5e117 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e117
          have b5e885 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e68 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68
          have b5e113209 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e885 x x
               have i₂ := b5e149
               grind)
            | exact superpose b5e149 b5e885
            | (have j0 := b5e885 x x
               grind)
            | exact resolve b5e885 b5e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e149 b5e885
          have b5e113216 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e113209
          have b5e113217 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e113216
          have b5e115070 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e36 (σ x) (σ x) x x
               have i₂ := b5e113217
               grind)
            | exact superpose b5e113217 b5e36
            | exact resolve b5e36 b5e113217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e117840 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e115070 (σ y) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e115070 X0 (σ y)
               grind)
            | exact superpose b5e115070 b5e24
            | exact resolve b5e24 b5e115070
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e117842 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e113217
               have i₂ := b5e115070 (σ x) X0
               grind)
            | (have i₁ := b5e113217
               have i₂ := b5e115070 X0 (σ x)
               grind)
            | exact superpose b5e115070 b5e113217
            | exact resolve b5e113217 b5e115070
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113217 b5e115070
          have b5e118249 : False := by grind
          exact b5e118249
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
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
        have b6e31 : (k x y) = (τ (σ x)) := by
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
        have b6e32 : x = (k x y) := by
          first
          | (have i₁ := b6e31
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e58 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
        have b6e60 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e58
        have b6e63 : y = (M.op x y) := by
          first
          | (have r₁ := b6e60
             have r₂ := b6e21
             grind)
          | exact resolve b6e60 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e66 : False := by grind
        exact b6e66
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e79 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 (σ x) (σ y) x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33
            | exact resolve b7e33 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e117 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e24
               have i₂ := b7e79 (σ y) X0
               grind)
            | (have i₁ := b7e24
               have i₂ := b7e79 X0 (σ y)
               grind)
            | exact superpose b7e79 b7e24
            | exact resolve b7e24 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e163 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ x) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e16 (σ x) X0
               have i₂ := b7e117 X0
               grind)
            | exact superpose b7e117 b7e16
            | (have j0 := b7e16 (σ x) X0
               grind)
            | (have r₁ := b7e16 (σ x) (σ x)
               have r₂ := b7e117 (σ x)
               grind)
            | exact resolve b7e16 b7e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e117
          have b7e1313 : (σ x) = (k (σ x) (σ x)) := by
            first
            | (have j0 := b7e163 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e163
          have b7e1314 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b7e1313
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e1313
            | exact resolve b7e1313 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1313
          have b7e1428 : (k x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e1314
               grind)
            | exact superpose b7e1314 b7e14
            | exact resolve b7e14 b7e1314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1314
          have b7e1440 : x = (k x x) := by
            first
            | (have i₁ := b7e1428
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1428
            | exact resolve b7e1428 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1428
          have b7e1571 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e1440
               grind)
            | exact superpose b7e1440 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e1440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1440
          have b7e1572 : x = (M.op x x) := by grind
          clear b7e1571
          have b7e1709 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 x x x x
               have i₂ := b7e1572
               grind)
            | exact superpose b7e1572 b7e33
            | exact resolve b7e33 b7e1572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e1958 : ∀ X0 : G, x ≠ (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e22
               have i₂ := b7e1709 y X0
               grind)
            | (have i₁ := b7e22
               have i₂ := b7e1709 X0 y
               grind)
            | exact superpose b7e1709 b7e22
            | exact resolve b7e22 b7e1709
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1960 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e1572
               have i₂ := b7e1709 x X0
               grind)
            | (have i₁ := b7e1572
               have i₂ := b7e1709 X0 x
               grind)
            | exact superpose b7e1709 b7e1572
            | exact resolve b7e1572 b7e1709
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1572 b7e1709
          have b7e2000 : False := by grind
          exact b7e2000
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e1160 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e53 x y
               grind)
            | exact superpose b8e53 b8e20
            | (have j1 := b8e53 x y
               grind)
            | exact resolve b8e20 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e1189 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1160
               have r₂ := b8e24
               grind)
            | exact resolve b8e1160 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1160
          have b8e1193 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1189
               have r₂ := b8e23
               grind)
            | exact resolve b8e1189 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1189
          have b8e1194 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1193
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1193
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1193 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1193
          have b8e1195 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e1194
          have b8e1196 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1195
               have r₂ := b8e22
               grind)
            | exact resolve b8e1195 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1195
          have b8e1197 : False := by grind
          exact b8e1197

/-- `Equation4437`: `x ◇ (y ◇ x) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyy_x_pxy_Equation4437 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = (M.op y x) := by grind
        have b0e21 : (σ x) = (M.op (σ y) (σ x)) := by grind
        have b0e22 : y = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e19
          | exact resolve b0e19 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e35 : ∀ X0 : G, (M.op x (M.op y x)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e12 x y X0
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e36 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e12 y x X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e38 : ∀ X0 : G, (M.op x X0) = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b0e36 X0
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e36
          | exact resolve b0e36 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36
        have b0e39 : ∀ X0 : G, (M.op y X0) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b0e35 X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e35
          | exact resolve b0e35 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e35
        have b0e57 : y ≠ y ∨ (M.op x x) = (k y x) := by
          first
          | (have i₁ := b0e15 y x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e15
          | (have j0 := b0e15 y x
             grind)
          | (have r₁ := b0e15 y x
             have r₂ := b0e22
             grind)
          | exact resolve b0e15 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e62 : (M.op x x) = (k y x) := by grind
        clear b0e57
        have b0e71 : x = (M.op x x) := by
          first
          | (have i₁ := b0e20
             have i₂ := b0e39 x
             grind)
          | exact superpose b0e39 b0e20
          | exact resolve b0e20 b0e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e84 : y = (k y (M.op x x)) ∨ y = (M.op (M.op x x) y) := by grind
        have b0e85 : y = (k y x) ∨ y = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b0e84
             have i₂ := b0e71
             grind)
          | exact superpose b0e71 b0e84
          | exact resolve b0e84 b0e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e84
        have b0e88 : y = (M.op x x) ∨ y = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b0e85
             have i₂ := b0e62
             grind)
          | exact superpose b0e62 b0e85
          | exact resolve b0e85 b0e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e62 b0e85
        have b0e90 : x = y ∨ y = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b0e88
             have i₂ := b0e71
             grind)
          | exact superpose b0e71 b0e88
          | exact resolve b0e88 b0e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e88
        have b0e92 : y = (M.op x (M.op x x)) ∨ x = y := by
          first
          | (have i₁ := b0e90
             have i₂ := b0e12 x x y
             grind)
          | exact superpose b0e12 b0e90
          | exact resolve b0e90 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e90
        have b0e94 : y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b0e92
             have i₂ := b0e38 (M.op x x)
             grind)
          | exact superpose b0e38 b0e92
          | exact resolve b0e92 b0e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38 b0e92
        have b0e95 : y = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b0e94
             have i₂ := b0e39 y
             grind)
          | exact superpose b0e39 b0e94
          | exact resolve b0e94 b0e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39 b0e94
        have b0e96 : x = y ∨ x = y := by
          first
          | (have i₁ := b0e95
             have i₂ := b0e71
             grind)
          | exact superpose b0e71 b0e95
          | exact resolve b0e95 b0e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e71 b0e95
        have b0e97 : x = y := by grind
        clear b0e96
        have b0e99 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e21
             have i₂ := b0e97
             grind)
          | exact superpose b0e97 b0e21
          | exact resolve b0e21 b0e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e101 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e24
             have i₂ := b0e97
             grind)
          | exact superpose b0e97 b0e24
          | exact resolve b0e24 b0e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24 b0e97
        have b0e104 : False := by grind
        exact b0e104
      · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : x = (M.op y x) := by grind
          have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
          have b1e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e42 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b1e13 y y x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e44 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b1e42 X0
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e42
            | exact resolve b1e42 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e42
          have b1e54 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
          have b1e56 : x ≠ x ∨ (M.op y y) = (k x y) := by
            first
            | (have i₁ := b1e16 x y
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e16
            | (have j0 := b1e16 x y
               grind)
            | (have r₁ := b1e16 x y
               have r₂ := b1e21
               grind)
            | exact resolve b1e16 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e58 : (M.op y y) = (k x y) := by grind
          clear b1e56
          have b1e59 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear b1e54
          have b1e60 : x = (k x y) := by
            first
            | (have i₁ := b1e58
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e58
            | exact resolve b1e58 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e58
          have b1e62 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b1e59
               have i₂ := b1e19 x y
               grind)
            | exact superpose b1e19 b1e59
            | exact resolve b1e59 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e59
          have b1e64 : (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b1e62
               have i₂ := b1e60
               grind)
            | exact superpose b1e60 b1e62
            | exact resolve b1e62 b1e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e60 b1e62
          have b1e91 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b1e13 (σ y) (σ y) x
               have i₂ := b1e64
               grind)
            | exact superpose b1e64 b1e13
            | exact resolve b1e13 b1e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e64
          have b1e95 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b1e91 X0
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e91
            | exact resolve b1e91 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e91
          have b1e100 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e95 (σ y)
               grind)
            | exact superpose b1e95 b1e20
            | exact resolve b1e20 b1e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e95
          have b1e111 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b1e100
               have i₂ := b1e44 y
               grind)
            | exact superpose b1e44 b1e100
            | exact resolve b1e100 b1e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e44 b1e100
          have b1e112 : False := by grind
          exact b1e112
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : x = (M.op y x) := by grind
          have b2e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
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
          have b2e40 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b2e13 y x X0
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e44 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e40 X1
               have i₂ := b2e40 X0
               grind)
            | exact superpose b2e40 b2e40
            | exact resolve b2e40 b2e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e40
          have b2e106 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X0 X0 X2
               have i₂ := b2e18 X0 X1
               grind)
            | (have i₁ := b2e13 X0 X1 X2
               have i₂ := b2e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b2e18 b2e13
            | (have j1 := b2e18 X1 X0
               grind)
            | exact resolve b2e13 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e144 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X0 X3) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e35 X0 X0 X2 X3
               have i₂ := b2e18 X0 X1
               grind)
            | (have i₁ := b2e35 X0 X1 X2 X3
               have i₂ := b2e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b2e18 b2e35
            | (have j1 := b2e18 X1 X0
               grind)
            | exact resolve b2e35 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e148 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e35 (σ y) (σ x) x x
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e35
            | exact resolve b2e35 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e35
          have b2e224 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b2e20
               have i₂ := b2e148 (σ y) X0
               grind)
            | (have i₁ := b2e20
               have i₂ := b2e148 X0 (σ y)
               grind)
            | exact superpose b2e148 b2e20
            | exact resolve b2e20 b2e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e490 : ∀ X0 X1 : G, (M.op (σ x) X1) ≠ (σ (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e224 X1
               have i₂ := b2e44 y X0
               grind)
            | (have i₁ := b2e224 X1
               have i₂ := b2e44 X0 y
               grind)
            | exact superpose b2e44 b2e224
            | exact resolve b2e224 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e44 b2e224
          have b2e1298 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e18 X0 X2
               have i₂ := b2e106 X0 X0 X1
               grind)
            | (have i₁ := b2e18 X2 X1
               have i₂ := b2e106 X2 X1 X2
               grind)
            | exact superpose b2e106 b2e18
            | (have j0 := b2e18 X0 X0
               have j1 := b2e106 X2 X0 X2
               grind)
            | exact resolve b2e18 b2e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e1399 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b2e106 X0 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e106
          have b2e1403 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b2e1399 X0 X1
               have j1 := b2e16 X0 X0
               grind)
            | (have r₁ := b2e1399 X0 X1
               have r₂ := b2e16 X0 X0
               grind)
            | exact resolve b2e1399 b2e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1399
          have b2e1417 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X2 ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b2e1298 X0 X1 X2
               have j1 := b2e16 X0 X0
               grind)
            | (have r₁ := b2e1298 X1 X0 X0
               have r₂ := b2e16 X0 X1
               grind)
            | (have r₁ := b2e1298 X0 X1 (M.op X1 (M.op X0 X1))
               have r₂ := b2e16 (M.op X0 X1) X1
               grind)
            | (have r₁ := b2e1298 X0 X1 X1
               have r₂ := b2e16 X0 X1
               grind)
            | exact resolve b2e1298 b2e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1298
          have b2e62759 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b2e144 X0 X1 X2 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e144
          have b2e203778 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b2e1417 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1417
          have b2e203780 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b2e203778 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e203778
          have b2e203797 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b2e203780 X0 X0
               have j1 := b2e62759 X0 X0 x
               grind)
            | (have r₁ := b2e203780 x x
               have r₂ := b2e62759 x (k x x) x
               grind)
            | (have r₁ := b2e203780 x x
               have r₂ := b2e62759 x x x
               grind)
            | (have r₁ := b2e203780 (M.op X0 x) x
               have r₂ := b2e62759 X0 (M.op (M.op X0 x) x) x
               grind)
            | exact resolve b2e203780 b2e62759
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e62759 b2e203780
          have b2e203851 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b2e203797 X0
               have j1 := b2e1403 X0 x
               grind)
            | (have r₁ := b2e203797 x
               have r₂ := b2e1403 x x
               grind)
            | exact resolve b2e203797 b2e1403
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1403 b2e203797
          have b2e203899 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b2e19 X0 X0
               have i₂ := b2e203851 (σ X0)
               grind)
            | exact superpose b2e203851 b2e19
            | exact resolve b2e19 b2e203851
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e203920 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b2e203899 X0
               have i₂ := b2e203851 X0
               grind)
            | exact superpose b2e203851 b2e203899
            | exact resolve b2e203899 b2e203851
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e203851 b2e203899
          have b2e205505 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b2e148 X0 (σ x)
               have i₂ := b2e203920 x
               grind)
            | exact superpose b2e203920 b2e148
            | exact resolve b2e148 b2e203920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e148 b2e203920
          have b2e205780 : False := by grind
          exact b2e205780
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : x = (M.op y x) := by grind
          have b3e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b3e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e20
            | exact resolve b3e20 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e41 : ∀ X0 : G, (M.op x (M.op y x)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b3e13 x y X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e42 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op x X0) := by
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
          have b3e44 : ∀ X0 : G, (M.op x X0) = (M.op y y) := by
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
          have b3e45 : ∀ X0 : G, (M.op y X0) = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b3e41 X0
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e41
            | exact resolve b3e41 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e41
          have b3e63 : y ≠ y ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b3e16 y x
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e16
            | (have j0 := b3e16 y x
               grind)
            | (have r₁ := b3e16 y x
               have r₂ := b3e24
               grind)
            | exact resolve b3e16 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e68 : (M.op x x) = (k y x) := by grind
          clear b3e63
          have b3e75 : x = (M.op x x) := by
            first
            | (have i₁ := b3e21
               have i₂ := b3e45 x
               grind)
            | exact superpose b3e45 b3e21
            | exact resolve b3e21 b3e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e89 : y = (k y (M.op x x)) ∨ y = (M.op (M.op x x) y) := by grind
          have b3e92 : y = (k y x) ∨ y = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b3e89
               have i₂ := b3e75
               grind)
            | exact superpose b3e75 b3e89
            | exact resolve b3e89 b3e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e89
          have b3e97 : y = (M.op x x) ∨ y = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b3e92
               have i₂ := b3e68
               grind)
            | exact superpose b3e68 b3e92
            | exact resolve b3e92 b3e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e68 b3e92
          have b3e100 : x = y ∨ y = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b3e97
               have i₂ := b3e75
               grind)
            | exact superpose b3e75 b3e97
            | exact resolve b3e97 b3e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e97
          have b3e103 : y = (M.op x (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b3e100
               have i₂ := b3e13 x x y
               grind)
            | exact superpose b3e13 b3e100
            | exact resolve b3e100 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e100
          have b3e105 : y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b3e103
               have i₂ := b3e44 (M.op x x)
               grind)
            | exact superpose b3e44 b3e103
            | exact resolve b3e103 b3e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e44 b3e103
          have b3e106 : y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b3e105
               have i₂ := b3e45 y
               grind)
            | exact superpose b3e45 b3e105
            | exact resolve b3e105 b3e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e45 b3e105
          have b3e107 : x = y ∨ x = y := by
            first
            | (have i₁ := b3e106
               have i₂ := b3e75
               grind)
            | exact superpose b3e75 b3e106
            | exact resolve b3e106 b3e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e75 b3e106
          have b3e108 : x = y := by grind
          clear b3e107
          have b3e112 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e26
               have i₂ := b3e108
               grind)
            | exact superpose b3e108 b3e26
            | exact resolve b3e26 b3e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26
          have b3e115 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e112
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e112
            | exact resolve b3e112 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e112
          have b3e117 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e115
               have i₂ := b3e108
               grind)
            | exact superpose b3e108 b3e115
            | exact resolve b3e115 b3e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e108 b3e115
          have b3e118 : False := by grind
          exact b3e118
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b4e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b4e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : x = (M.op y x) := by grind
            have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b4e25 : y ≠ (M.op x y) := by grind
            have b4e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e40 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b4e14 y y x
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e14
              | exact resolve b4e14 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e42 : ∀ X0 : G, x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b4e40 X0
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e40
              | exact resolve b4e40 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e40
            have b4e46 : x ≠ y := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e42 y
                 grind)
              | exact superpose b4e42 b4e25
              | exact resolve b4e25 b4e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e53 : ∀ X0 : G, x ≠ X0 ∨ (k X0 x) = (M.op x x) := by
              intro X0
              first
              | (have i₁ := b4e17 X0 x
                 have i₂ := b4e42 X0
                 grind)
              | exact superpose b4e42 b4e17
              | (have j0 := b4e17 X0 x
                 grind)
              | (have r₁ := b4e17 x x
                 have r₂ := b4e42 x
                 grind)
              | exact resolve b4e17 b4e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e58 : ∀ X0 : G, x ≠ X0 ∨ x = (k X0 x) := by
              intro X0
              first
              | (have i₁ := b4e53 X0
                 have i₂ := b4e42 x
                 grind)
              | exact superpose b4e42 b4e53
              | (have j0 := b4e53 X0
                 grind)
              | (have r₁ := b4e53 (M.op x X0)
                 have r₂ := b4e42 X0
                 grind)
              | exact resolve b4e53 b4e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e42 b4e53
            have b4e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b4e20 X0 X1
                 have i₂ := b4e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b4e19 b4e20
              | (have j1 := b4e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b4e20 b4e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e117 : x = (k x x) := by
              first
              | (have j0 := b4e58 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e58
            have b4e2310 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b4e24
                 have i₂ := b4e74 x x
                 grind)
              | exact superpose b4e74 b4e24
              | (have j1 := b4e74 x x
                 grind)
              | exact resolve b4e24 b4e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e74
            have b4e2415 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b4e2310
            have b4e2465 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b4e2415
                 have i₂ := b4e117
                 grind)
              | exact superpose b4e117 b4e2415
              | exact resolve b4e2415 b4e117
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e117 b4e2415
            have b4e2495 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b4e2465
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e2465
              | exact resolve b4e2465 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e2465
            have b4e2496 : (σ x) = (σ y) := by grind
            clear b4e2495
            have b4e2515 : y = (τ (σ x)) := by
              first
              | (have i₁ := b4e15 y
                 have i₂ := b4e2496
                 grind)
              | exact superpose b4e2496 b4e15
              | exact resolve b4e15 b4e2496
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e2496
            have b4e2533 : x = y := by
              first
              | (have i₁ := b4e2515
                 have i₂ := b4e15 x
                 grind)
              | exact superpose b4e15 b4e2515
              | exact resolve b4e2515 b4e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e2515
            have b4e2538 : False := by grind
            exact b4e2538
          · have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : x = (M.op y x) := by grind
            have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b5e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b5e26 : x ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e58 : x ≠ x ∨ (M.op y y) = (k x y) := by
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
            have b5e60 : (M.op y y) = (k x y) := by grind
            clear b5e58
            have b5e65 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b5e66 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e65
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e65 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e65
            have b5e68 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b5e66
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e66
              | exact resolve b5e66 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e66
            have b5e69 : (σ x) = (σ (M.op y y)) := by
              first
              | (have i₁ := b5e68
                 have i₂ := b5e60
                 grind)
              | exact superpose b5e60 b5e68
              | exact resolve b5e68 b5e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e60 b5e68
            have b5e72 : (M.op y y) = (τ (σ x)) := by
              first
              | (have i₁ := b5e15 (M.op y y)
                 have i₂ := b5e69
                 grind)
              | exact superpose b5e69 b5e15
              | exact resolve b5e15 b5e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e69
            have b5e73 : x = (M.op y y) := by
              first
              | (have i₁ := b5e72
                 have i₂ := b5e15 x
                 grind)
              | exact superpose b5e15 b5e72
              | exact resolve b5e72 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e72
            have b5e76 : False := by grind
            exact b5e76
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e21 : x = (M.op y x) := by grind
          have b6e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e20
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e20
            | exact resolve b6e20 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e39 : ∀ X0 : G, (M.op x (M.op y x)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b6e13 x y X0
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e40 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op x X0) := by
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
          have b6e42 : ∀ X0 : G, (M.op x X0) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b6e40 X0
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e40
            | exact resolve b6e40 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e40
          have b6e43 : ∀ X0 : G, (M.op y X0) = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b6e39 X0
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e39
            | exact resolve b6e39 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e39
          have b6e60 : y ≠ y ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b6e16 y x
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e16
            | (have j0 := b6e16 y x
               grind)
            | (have r₁ := b6e16 y x
               have r₂ := b6e24
               grind)
            | exact resolve b6e16 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e65 : (M.op x x) = (k y x) := by grind
          clear b6e60
          have b6e71 : x = (M.op x x) := by
            first
            | (have i₁ := b6e21
               have i₂ := b6e43 x
               grind)
            | exact superpose b6e43 b6e21
            | exact resolve b6e21 b6e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e84 : y = (k y (M.op x x)) ∨ y = (M.op (M.op x x) y) := by grind
          have b6e87 : y = (k y x) ∨ y = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b6e84
               have i₂ := b6e71
               grind)
            | exact superpose b6e71 b6e84
            | exact resolve b6e84 b6e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e84
          have b6e91 : y = (M.op x x) ∨ y = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b6e87
               have i₂ := b6e65
               grind)
            | exact superpose b6e65 b6e87
            | exact resolve b6e87 b6e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e65 b6e87
          have b6e93 : x = y ∨ y = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b6e91
               have i₂ := b6e71
               grind)
            | exact superpose b6e71 b6e91
            | exact resolve b6e91 b6e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e91
          have b6e95 : y = (M.op x (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b6e93
               have i₂ := b6e13 x x y
               grind)
            | exact superpose b6e13 b6e93
            | exact resolve b6e93 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e93
          have b6e97 : y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b6e95
               have i₂ := b6e42 (M.op x x)
               grind)
            | exact superpose b6e42 b6e95
            | exact resolve b6e95 b6e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e42 b6e95
          have b6e98 : y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b6e97
               have i₂ := b6e43 y
               grind)
            | exact superpose b6e43 b6e97
            | exact resolve b6e97 b6e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e43 b6e97
          have b6e99 : x = y ∨ x = y := by
            first
            | (have i₁ := b6e98
               have i₂ := b6e71
               grind)
            | exact superpose b6e71 b6e98
            | exact resolve b6e98 b6e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e98
          have b6e100 : x = y := by grind
          clear b6e99
          have b6e104 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e26
               have i₂ := b6e100
               grind)
            | exact superpose b6e100 b6e26
            | exact resolve b6e26 b6e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26
          have b6e114 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e13 X0 X0 X2
               have i₂ := b6e18 X0 X1
               grind)
            | (have i₁ := b6e13 X0 X1 X2
               have i₂ := b6e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b6e18 b6e13
            | (have j1 := b6e18 X1 X0
               grind)
            | exact resolve b6e13 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e117 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
          have b6e119 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e117 X0
               have i₂ := b6e100
               grind)
            | exact superpose b6e100 b6e117
            | (have j0 := b6e117 X0
               grind)
            | exact resolve b6e117 b6e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e100 b6e117
          have b6e120 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b6e16 x x
               have i₂ := b6e71
               grind)
            | exact superpose b6e71 b6e16
            | (have r₁ := b6e16 x x
               have r₂ := b6e71
               grind)
            | exact resolve b6e16 b6e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e71
          have b6e124 : x = (k x x) := by grind
          clear b6e120
          have b6e1370 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b6e114 X0 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e114
          have b6e1376 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b6e1370 X0 X1
               have j1 := b6e16 X0 X0
               grind)
            | (have r₁ := b6e1370 X0 X1
               have r₂ := b6e16 X0 X0
               grind)
            | exact resolve b6e1370 b6e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1370
          have b6e1505 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have j0 := b6e119 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e119
          have b6e1506 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
            first
            | (have j1 := b6e1376 (σ x) x
               grind)
            | (have r₁ := b6e1505
               have r₂ := b6e1376 (σ x) (σ x)
               grind)
            | exact resolve b6e1505 b6e1376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1376 b6e1505
          have b6e1507 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
            first
            | (have i₁ := b6e1506
               have i₂ := b6e19 x x
               grind)
            | exact superpose b6e19 b6e1506
            | exact resolve b6e1506 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1506
          have b6e1508 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e1507
               have i₂ := b6e124
               grind)
            | exact superpose b6e124 b6e1507
            | exact resolve b6e1507 b6e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e124 b6e1507
          have b6e1509 : False := by grind
          exact b6e1509
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b7e22 : x = (M.op y x) := by grind
            have b7e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b7e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b7e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e36 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b7e14 y y x
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e41 : ∀ X0 : G, x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b7e36 X0
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e36
              | exact resolve b7e36 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e36
            have b7e51 : x ≠ x ∨ (M.op y y) = (k x y) := by
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
            have b7e53 : (M.op y y) = (k x y) := by grind
            clear b7e51
            have b7e54 : x = (k x y) := by
              first
              | (have i₁ := b7e53
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e53
              | exact resolve b7e53 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e53
            have b7e73 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b7e24
                 have i₂ := b7e19 (σ x) X0
                 grind)
              | (have i₁ := b7e24
                 have i₂ := b7e19 X0 (M.op (σ x) (σ x))
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
            have b7e2464 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b7e73 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e73
            have b7e2465 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b7e2464
                 have r₂ := b7e23
                 grind)
              | exact resolve b7e2464 b7e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e2464
            have b7e2466 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b7e2465
                 have i₂ := b7e20 x y
                 grind)
              | exact superpose b7e20 b7e2465
              | exact resolve b7e2465 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e2465
            have b7e2467 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b7e2466
                 have i₂ := b7e54
                 grind)
              | exact superpose b7e54 b7e2466
              | exact resolve b7e2466 b7e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e54 b7e2466
            have b7e2470 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b7e21
                 have i₂ := b7e2467
                 grind)
              | exact superpose b7e2467 b7e21
              | exact resolve b7e21 b7e2467
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e2467
            have b7e2496 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b7e2470
                 have i₂ := b7e41 y
                 grind)
              | exact superpose b7e41 b7e2470
              | exact resolve b7e2470 b7e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e41 b7e2470
            have b7e2497 : False := by grind
            exact b7e2497
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b8e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : x = (M.op y x) := by grind
            have b8e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b8e25 : y ≠ (M.op x y) := by grind
            have b8e26 : x ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X0 X1 X3
                 have i₂ := b8e14 X0 X1 X2
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e34 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b8e14 y x X0
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X0 X1 (M.op X2 (M.op X0 X1))
                 have i₂ := b8e14 (M.op X0 X1) X2 X3
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e40 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e34 X1
                 have i₂ := b8e34 X0
                 grind)
              | exact superpose b8e34 b8e34
              | exact resolve b8e34 b8e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e53 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X2 ∨ (k X2 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e17 X2 (M.op X0 X1)
                 have i₂ := b8e14 X0 X1 X2
                 grind)
              | exact superpose b8e14 b8e17
              | (have j0 := b8e17 X2 (M.op X0 X1)
                 grind)
              | (have r₁ := b8e17 (M.op X0 (M.op X1 X0)) (M.op X0 X1)
                 have r₂ := b8e14 X0 X1 (M.op X0 (M.op X1 X0))
                 grind)
              | exact resolve b8e17 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e55 : x ≠ x ∨ (M.op y y) = (k x y) := by
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
            have b8e57 : (M.op y y) = (k x y) := by grind
            clear b8e55
            have b8e59 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X2 ∨ (M.op X0 (M.op X1 X0)) = (k X2 (M.op X0 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e53 X0 X1 X2
                 have i₂ := b8e14 X0 X1 (M.op X0 X1)
                 grind)
              | exact superpose b8e14 b8e53
              | (have j0 := b8e53 X0 X1 X2
                 grind)
              | (have r₁ := b8e53 X0 X1 (M.op (M.op X0 X1) X2)
                 have r₂ := b8e14 X0 X1 X2
                 grind)
              | (have r₁ := b8e53 (M.op X0 X1) X1 (M.op X0 (M.op X1 X0))
                 have r₂ := b8e14 X0 X1 (M.op X1 (M.op X0 X1))
                 grind)
              | exact resolve b8e53 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e53
            have b8e75 : ∀ X0 X1 : G, (M.op x X1) = (M.op y (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e34 X1
                 have i₂ := b8e40 y X0
                 grind)
              | (have i₁ := b8e34 X1
                 have i₂ := b8e40 X0 y
                 grind)
              | exact superpose b8e40 b8e34
              | exact resolve b8e34 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e76 : ∀ X0 : G, y ≠ (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b8e25
                 have i₂ := b8e40 y X0
                 grind)
              | (have i₁ := b8e25
                 have i₂ := b8e40 X0 y
                 grind)
              | exact superpose b8e40 b8e25
              | exact resolve b8e25 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
            have b8e94 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X0 X0 X2
                 have i₂ := b8e19 X0 X1
                 grind)
              | (have i₁ := b8e14 X0 X1 X2
                 have i₂ := b8e19 X0 (M.op X1 X0)
                 grind)
              | exact superpose b8e19 b8e14
              | (have j1 := b8e19 X1 X0
                 grind)
              | exact resolve b8e14 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e97 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
            have b8e101 : y ≠ (M.op y (M.op x y)) := by
              first
              | (have i₁ := b8e76 x
                 have i₂ := b8e34 x
                 grind)
              | exact superpose b8e34 b8e76
              | exact resolve b8e76 b8e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e34 b8e76
            have b8e111 : ∀ X0 : G, y ≠ (M.op y (M.op x X0)) := by
              intro X0
              first
              | (have i₁ := b8e101
                 have i₂ := b8e40 y X0
                 grind)
              | (have i₁ := b8e101
                 have i₂ := b8e40 X0 y
                 grind)
              | exact superpose b8e40 b8e101
              | exact resolve b8e101 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e101
            have b8e206 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
              intro X0 X1 X2 X3 X4 X5
              first
              | (have i₁ := b8e37 X0 X1 X2 (M.op X3 (M.op (M.op X0 X1) X2))
                 have i₂ := b8e37 (M.op (M.op X0 X1) X2) X3 X4 X5
                 grind)
              | exact superpose b8e37 b8e37
              | exact resolve b8e37 b8e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e224 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b8e14 (M.op (M.op X0 X1) X2) X3 X4
                 have i₂ := b8e37 X0 X1 X2 (M.op X3 (M.op (M.op X0 X1) X2))
                 grind)
              | exact superpose b8e37 b8e14
              | exact resolve b8e14 b8e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e37
            have b8e248 : ∀ X0 X1 : G, (M.op x X1) = (M.op y (M.op y (M.op x X0))) := by
              intro X0 X1
              first
              | (have i₁ := b8e75 x X1
                 have i₂ := b8e75 X0 x
                 grind)
              | exact superpose b8e75 b8e75
              | exact resolve b8e75 b8e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e258 : ∀ X0 : G, y ≠ (M.op y (M.op y (M.op x X0))) := by
              intro X0
              first
              | (have i₁ := b8e111 x
                 have i₂ := b8e75 X0 x
                 grind)
              | exact superpose b8e75 b8e111
              | exact resolve b8e111 b8e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e75 b8e111
            have b8e919 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X0 (M.op X1 X0)) (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have j0 := b8e59 X0 X1 (M.op X0 (M.op X1 X0))
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e59
            have b8e968 : ∀ X0 : G, x = (M.op x X0) ∨ x = (k y x) ∨ y = (M.op x y) := by
              intro X0
              first
              | (have i₁ := b8e94 x y x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e94
              | (have j0 := b8e94 x y x
                 grind)
              | exact resolve b8e94 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e1033 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e23
                 have i₂ := b8e94 (σ x) (σ y) X0
                 grind)
              | (have i₁ := b8e23
                 have i₂ := b8e94 (σ y) x (σ x)
                 grind)
              | exact superpose b8e94 b8e23
              | (have j1 := b8e94 (σ x) (σ y) x
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e94 (σ y) (σ x) x
                 grind)
              | exact resolve b8e23 b8e94
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e1046 : ∀ X0 : G, x ≠ (M.op y X0) ∨ (M.op y y) = (k y y) ∨ y = (M.op y y) := by
              intro X0
              first
              | (have i₁ := b8e26
                 have i₂ := b8e94 y y X0
                 grind)
              | (have i₁ := b8e26
                 have i₂ := b8e94 y x y
                 grind)
              | exact superpose b8e94 b8e26
              | (have j1 := b8e94 y y x
                 grind)
              | exact resolve b8e26 b8e94
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e94
            have b8e1109 : ∀ X0 : G, x ≠ (M.op y X0) ∨ (M.op y y) = (k y y) := by
              intro X0
              first
              | (have j0 := b8e1046 X0
                 have j1 := b8e17 y y
                 grind)
              | (have r₁ := b8e1046 X0
                 have r₂ := b8e17 y y
                 grind)
              | exact resolve b8e1046 b8e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1046
            have b8e1113 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e1033 X0
                 have i₂ := b8e20 y x
                 grind)
              | exact superpose b8e20 b8e1033
              | (have j0 := b8e1033 X0
                 grind)
              | exact resolve b8e1033 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1033
            have b8e1125 : ∀ X0 : G, x = (M.op x X0) ∨ x = (k y x) := by
              intro X0
              first
              | (have j0 := b8e968 X0
                 grind)
              | (have r₁ := b8e968 X0
                 have r₂ := b8e25
                 grind)
              | exact resolve b8e968 b8e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e968
            have b8e1190 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b8e97 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e97
            have b8e1191 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b8e1190
                 have r₂ := b8e23
                 grind)
              | exact resolve b8e1190 b8e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1190
            have b8e1192 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e1191
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e1191
              | exact resolve b8e1191 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1191
            have b8e1193 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b8e1192
                 have i₂ := b8e57
                 grind)
              | exact superpose b8e57 b8e1192
              | exact resolve b8e1192 b8e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e57 b8e1192
            have b8e1376 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e90 X0 X0
                 have i₂ := b8e90 X0 X1
                 grind)
              | exact superpose b8e90 b8e90
              | (have j0 := b8e90 X1 X0
                 have j1 := b8e90 X1 X0
                 grind)
              | exact resolve b8e90 b8e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e1411 : ∀ X0 X1 : G, (σ X0) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e17 (σ X0) (σ X0)
                 have i₂ := b8e90 X0 X1
                 grind)
              | exact superpose b8e90 b8e17
              | (have j1 := b8e90 X1 X0
                 grind)
              | (have r₁ := b8e17 (σ X1) (σ X1)
                 have r₂ := b8e90 X1 X1
                 grind)
              | (have r₁ := b8e17 (σ X0) (σ X1)
                 have r₂ := b8e90 X0 X1
                 grind)
              | exact resolve b8e17 b8e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e1447 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b8e90 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e90
            have b8e1448 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b8e1447 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1447
            have b8e1458 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b8e1376 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1376
            have b8e1471 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X0) ≠ (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e1411 X0 X1
                 have i₂ := b8e20 X1 X1
                 grind)
              | exact superpose b8e20 b8e1411
              | (have j0 := b8e1411 X0 X1
                 grind)
              | exact resolve b8e1411 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1411
            have b8e1491 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b8e1471 X0 X1
                 have j1 := b8e1458 X0 X1
                 grind)
              | (have r₁ := b8e1471 X0 X1
                 have r₂ := b8e1458 X0 X1
                 grind)
              | (have r₁ := b8e1471 X1 X0
                 have r₂ := b8e1458 X0 X1
                 grind)
              | (have r₁ := b8e1471 X0 (k X1 X1)
                 have r₂ := b8e1458 X0 X1
                 grind)
              | exact resolve b8e1471 b8e1458
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1458 b8e1471
            have b8e2319 : x ≠ x ∨ (M.op y y) = (k y y) := by
              first
              | (have i₁ := b8e1109 x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e1109
              | (have r₁ := b8e1109 x
                 have r₂ := b8e22
                 grind)
              | exact resolve b8e1109 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1109
            have b8e2329 : (M.op y y) = (k y y) := by grind
            clear b8e2319
            have b8e2639 : ∀ X0 : G, y ≠ (M.op y (M.op y (M.op y (M.op y (M.op x X0))))) := by
              intro X0
              first
              | (have i₁ := b8e258 x
                 have i₂ := b8e248 X0 x
                 grind)
              | exact superpose b8e248 b8e258
              | exact resolve b8e258 b8e248
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e248 b8e258
            have b8e12199 : ∀ X0 X1 : G, (M.op x X0) = (k (M.op x X0) (M.op x X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e919 x X1
                 have i₂ := b8e40 (M.op X1 x) X1
                 grind)
              | (have i₁ := b8e919 x X1
                 have i₂ := b8e40 X0 (M.op X1 x)
                 grind)
              | exact superpose b8e40 b8e919
              | exact resolve b8e919 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e40 b8e919
            have b8e12499 : ∀ X0 : G, (σ (M.op x X0)) ≠ (σ (M.op x X0)) ∨ (σ (M.op x X0)) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
              intro X0
              first
              | (have i₁ := b8e1448 (M.op x X0)
                 have i₂ := b8e12199 X0 X0
                 grind)
              | exact superpose b8e12199 b8e1448
              | (have j0 := b8e1448 (M.op x X0)
                 grind)
              | exact resolve b8e1448 b8e12199
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1448 b8e12199
            have b8e12507 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
              intro X0
              first
              | (have j0 := b8e12499 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e12499
            have b8e81517 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (M.op (M.op (M.op (M.op (σ (M.op x X0)) X1) X2) X3) X4) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b8e206 (σ (M.op x X0)) (σ (M.op x X0)) X2 X3 X4 x
                 have i₂ := b8e12507 X0
                 grind)
              | exact superpose b8e12507 b8e206
              | exact resolve b8e206 b8e12507
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e206
            have b8e81525 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (M.op (M.op (M.op (σ (M.op x X0)) X1) X2) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e224 (σ (M.op x X0)) (σ (M.op x X0)) X2 X3 x
                 have i₂ := b8e12507 X0
                 grind)
              | exact superpose b8e12507 b8e224
              | exact resolve b8e224 b8e12507
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e224
            have b8e81611 : ∀ X0 X1 X2 X3 : G, (σ (M.op x X0)) = (M.op (M.op (M.op (σ (M.op x X0)) X1) X2) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e81525 X0 X1 X2 X3
                 have i₂ := b8e12507 X0
                 grind)
              | exact superpose b8e12507 b8e81525
              | exact resolve b8e81525 b8e12507
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e81525
            have b8e81614 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op x X0)) = (M.op (M.op (M.op (M.op (σ (M.op x X0)) X1) X2) X3) X4) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b8e81517 X0 X1 X2 X3 X4
                 have i₂ := b8e12507 X0
                 grind)
              | exact superpose b8e12507 b8e81517
              | exact resolve b8e81517 b8e12507
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e12507 b8e81517
            have b8e81659 : ∀ X0 X4 : G, (σ (M.op x X0)) = (M.op (σ (M.op x X0)) X4) := by
              intro X0 X4
              first
              | (have i₁ := b8e81614 X0 x x x X4
                 have i₂ := b8e81611 X0 x x x
                 grind)
              | exact superpose b8e81611 b8e81614
              | exact resolve b8e81614 b8e81611
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e81611 b8e81614
            have b8e82138 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ x = (k y x) := by
              intro X1
              first
              | (have i₁ := b8e81659 x x
                 have i₂ := b8e1125 x
                 grind)
              | exact superpose b8e1125 b8e81659
              | exact resolve b8e81659 b8e1125
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1125 b8e81659
            have b8e83003 : (σ x) = (σ (M.op y y)) ∨ x = (k y x) := by
              first
              | (have i₁ := b8e1193
                 have i₂ := b8e82138 (σ y)
                 grind)
              | exact superpose b8e82138 b8e1193
              | exact resolve b8e1193 b8e82138
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e82138
            have b8e83682 : (M.op y y) = (τ (σ x)) ∨ x = (k y x) := by
              first
              | (have i₁ := b8e15 (M.op y y)
                 have i₂ := b8e83003
                 grind)
              | exact superpose b8e83003 b8e15
              | exact resolve b8e15 b8e83003
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e83003
            have b8e83712 : x = (M.op y y) ∨ x = (k y x) := by
              first
              | (have i₁ := b8e83682
                 have i₂ := b8e15 x
                 grind)
              | exact superpose b8e15 b8e83682
              | exact resolve b8e83682 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e83682
            have b8e83714 : x = (k y x) := by
              first
              | (have r₁ := b8e83712
                 have r₂ := b8e26
                 grind)
              | exact resolve b8e83712 b8e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e83712
            have b8e165231 : (σ x) ≠ (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
              first
              | (have i₁ := b8e1113 (σ y)
                 have i₂ := b8e1193
                 grind)
              | exact superpose b8e1193 b8e1113
              | exact resolve b8e1113 b8e1193
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1113
            have b8e165349 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
              first
              | (have i₁ := b8e165231
                 have i₂ := b8e83714
                 grind)
              | exact superpose b8e83714 b8e165231
              | exact resolve b8e165231 b8e83714
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e165231
            have b8e165365 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
              first
              | (have r₁ := b8e165349
                 have r₂ := b8e23
                 grind)
              | exact resolve b8e165349 b8e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e165349
            have b8e165583 : (σ x) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b8e23
                 have i₂ := b8e1491 x y
                 grind)
              | exact superpose b8e1491 b8e23
              | (have j1 := b8e1491 x y
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e1491 y x
                 grind)
              | exact resolve b8e23 b8e1491
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1491
            have b8e166001 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b8e165583
                 have i₂ := b8e83714
                 grind)
              | exact superpose b8e83714 b8e165583
              | exact resolve b8e165583 b8e83714
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e83714 b8e165583
            have b8e166002 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
            clear b8e166001
            have b8e166056 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b8e166002
                 have i₂ := b8e2329
                 grind)
              | exact superpose b8e2329 b8e166002
              | exact resolve b8e166002 b8e2329
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2329 b8e166002
            have b8e166086 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
              first
              | (have i₁ := b8e166056
                 have i₂ := b8e1193
                 grind)
              | exact superpose b8e1193 b8e166056
              | exact resolve b8e166056 b8e1193
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1193 b8e166056
            have b8e166097 : (σ y) = (σ (M.op y y)) := by
              first
              | (have r₁ := b8e166086
                 have r₂ := b8e165365
                 grind)
              | exact resolve b8e166086 b8e165365
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e165365 b8e166086
            have b8e166119 : (M.op y y) = (τ (σ y)) := by
              first
              | (have i₁ := b8e15 (M.op y y)
                 have i₂ := b8e166097
                 grind)
              | exact superpose b8e166097 b8e15
              | exact resolve b8e15 b8e166097
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e166097
            have b8e166179 : y = (M.op y y) := by
              first
              | (have i₁ := b8e166119
                 have i₂ := b8e15 y
                 grind)
              | exact superpose b8e15 b8e166119
              | exact resolve b8e166119 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e166119
            have b8e167353 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e32 y y x x
                 have i₂ := b8e166179
                 grind)
              | exact superpose b8e166179 b8e32
              | exact resolve b8e32 b8e166179
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e32
            have b8e170651 : ∀ X0 : G, y ≠ (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b8e2639 x
                 have i₂ := b8e167353 (M.op y (M.op y (M.op y (M.op x x)))) X0
                 grind)
              | (have i₁ := b8e2639 x
                 have i₂ := b8e167353 X0 (M.op y (M.op y (M.op y (M.op x x))))
                 grind)
              | exact superpose b8e167353 b8e2639
              | exact resolve b8e2639 b8e167353
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2639
            have b8e170660 : ∀ X0 : G, y = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b8e166179
                 have i₂ := b8e167353 y X0
                 grind)
              | (have i₁ := b8e166179
                 have i₂ := b8e167353 X0 y
                 grind)
              | exact superpose b8e167353 b8e166179
              | exact resolve b8e166179 b8e167353
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e166179 b8e167353
            have b8e171190 : False := by grind
            exact b8e171190
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : x ≠ (M.op y x) := by grind
          have b9e22 : y = (M.op x x) := by grind
          have b9e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          have b9e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e20
            | exact resolve b9e20 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e42 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b9e13 x x x
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e13
            | exact resolve b9e13 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e45 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b9e42 X0
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e42
            | exact resolve b9e42 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e42
          have b9e51 : x ≠ y := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e45 x
               grind)
            | exact superpose b9e45 b9e21
            | exact resolve b9e21 b9e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e45
          have b9e55 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b9e16 (σ x) (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 (σ x) (σ y)
               grind)
            | (have r₁ := b9e16 (σ x) (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e60 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear b9e55
          have b9e63 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b9e60
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e60
            | exact resolve b9e60 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e60
          have b9e66 : x = (k x y) ∨ x = (M.op y x) := by grind
          have b9e70 : x = (k x y) := by
            first
            | (have r₁ := b9e66
               have r₂ := b9e21
               grind)
            | exact resolve b9e66 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e66
          have b9e143 : ∀ X0 : G, (M.op (σ y) (σ (k x y))) = (M.op (σ (k x y)) X0) := by
            intro X0
            first
            | (have i₁ := b9e13 (σ y) (σ y) x
               have i₂ := b9e63
               grind)
            | exact superpose b9e63 b9e13
            | exact resolve b9e13 b9e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e63
          have b9e144 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b9e143 X0
               have i₂ := b9e70
               grind)
            | exact superpose b9e70 b9e143
            | exact resolve b9e143 b9e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e70 b9e143
          have b9e150 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b9e144 X0
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e144
            | exact resolve b9e144 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e144
          have b9e160 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ x) (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b9e16 X0 (σ x)
               have i₂ := b9e150 X0
               grind)
            | exact superpose b9e150 b9e16
            | (have j0 := b9e16 X0 (σ x)
               grind)
            | (have r₁ := b9e16 (σ x) (σ x)
               have r₂ := b9e150 (σ x)
               grind)
            | exact resolve b9e16 b9e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e164 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b9e26
               have i₂ := b9e150 (σ y)
               grind)
            | exact superpose b9e150 b9e26
            | exact resolve b9e26 b9e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26
          have b9e167 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ x) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b9e160 X0
               have i₂ := b9e150 (σ x)
               grind)
            | exact superpose b9e150 b9e160
            | (have j0 := b9e160 X0
               grind)
            | (have r₁ := b9e160 (M.op (σ x) X0)
               have r₂ := b9e150 X0
               grind)
            | exact resolve b9e160 b9e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e150 b9e160
          have b9e1181 : (σ x) = (k (σ x) (σ x)) := by
            first
            | (have j0 := b9e167 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e167
          have b9e1182 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b9e1181
               have i₂ := b9e19 x x
               grind)
            | exact superpose b9e19 b9e1181
            | exact resolve b9e1181 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e1181
          have b9e1203 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b9e1182
               have i₂ := b9e18 x x
               grind)
            | exact superpose b9e18 b9e1182
            | (have j1 := b9e18 x x
               grind)
            | exact resolve b9e1182 b9e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e1182
          have b9e1209 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b9e1203
          have b9e1215 : (σ x) = (σ y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b9e1209
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e1209
            | exact resolve b9e1209 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e1209
          have b9e1217 : x = (M.op x x) := by
            first
            | (have r₁ := b9e1215
               have r₂ := b9e164
               grind)
            | exact resolve b9e1215 b9e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e164 b9e1215
          have b9e1446 : x = y := by
            first
            | (have i₁ := b9e22
               have i₂ := b9e1217
               grind)
            | exact superpose b9e1217 b9e22
            | exact resolve b9e22 b9e1217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e1217
          have b9e1470 : False := by grind
          exact b9e1470
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b10e22 : x ≠ (M.op y x) := by grind
            have b10e23 : y = (M.op x x) := by grind
            have b10e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e40 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b10e14 x x x
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e14
              | exact resolve b10e14 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e48 : x ≠ (M.op x y) := by
              first
              | (have i₁ := b10e22
                 have i₂ := b10e40 x
                 grind)
              | exact superpose b10e40 b10e22
              | exact resolve b10e22 b10e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e49 : x = (M.op x y) := by
              first
              | (have i₁ := b10e26
                 have i₂ := b10e40 y
                 grind)
              | exact superpose b10e40 b10e26
              | exact resolve b10e26 b10e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e40
            have b10e50 : False := by grind
            exact b10e50
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : x ≠ (M.op y x) := by grind
            have b11e23 : y = (M.op x x) := by grind
            have b11e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b11e26 : x ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e39 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b11e14 x x x
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e46 : x ≠ (M.op x y) := by
              first
              | (have i₁ := b11e26
                 have i₂ := b11e39 y
                 grind)
              | exact superpose b11e39 b11e26
              | exact resolve b11e26 b11e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e39
            have b11e52 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
            have b11e55 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
            clear b11e52
            have b11e57 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b11e55
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e55
              | exact resolve b11e55 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e55
            have b11e60 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b11e63 : x = (k x y) := by
              first
              | (have r₁ := b11e60
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e60 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e60
            have b11e114 : ∀ X0 : G, (M.op (σ y) (σ (k x y))) = (M.op (σ (k x y)) X0) := by
              intro X0
              first
              | (have i₁ := b11e14 (σ y) (σ y) x
                 have i₂ := b11e57
                 grind)
              | exact superpose b11e57 b11e14
              | exact resolve b11e14 b11e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e57
            have b11e115 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b11e114 X0
                 have i₂ := b11e63
                 grind)
              | exact superpose b11e63 b11e114
              | exact resolve b11e114 b11e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e63 b11e114
            have b11e121 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b11e115 X0
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e115
              | exact resolve b11e115 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e115
            have b11e177 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ x) (σ x)) = (k X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b11e17 X0 (σ x)
                 have i₂ := b11e121 X0
                 grind)
              | exact superpose b11e121 b11e17
              | (have j0 := b11e17 X0 (σ x)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ x)
                 have r₂ := b11e121 (σ x)
                 grind)
              | exact resolve b11e17 b11e121
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e184 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ x) = (k X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b11e177 X0
                 have i₂ := b11e121 (σ x)
                 grind)
              | exact superpose b11e121 b11e177
              | (have j0 := b11e177 X0
                 grind)
              | (have r₁ := b11e177 (M.op (σ x) X0)
                 have r₂ := b11e121 X0
                 grind)
              | exact resolve b11e177 b11e121
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e121 b11e177
            have b11e1214 : (σ x) = (k (σ x) (σ x)) := by
              first
              | (have j0 := b11e184 (σ x)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e184
            have b11e1215 : (σ x) = (σ (k x x)) := by
              first
              | (have i₁ := b11e1214
                 have i₂ := b11e20 x x
                 grind)
              | exact superpose b11e20 b11e1214
              | exact resolve b11e1214 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1214
            have b11e1334 : (k x x) = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 (k x x)
                 have i₂ := b11e1215
                 grind)
              | exact superpose b11e1215 b11e15
              | exact resolve b11e15 b11e1215
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1215
            have b11e1336 : x = (k x x) := by
              first
              | (have i₁ := b11e1334
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e1334
              | exact resolve b11e1334 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1334
            have b11e1424 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b11e19 x x
                 have i₂ := b11e1336
                 grind)
              | exact superpose b11e1336 b11e19
              | (have j0 := b11e19 x x
                 grind)
              | exact resolve b11e19 b11e1336
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1336
            have b11e1425 : x = (M.op x x) := by grind
            clear b11e1424
            have b11e1712 : x = y := by
              first
              | (have i₁ := b11e23
                 have i₂ := b11e1425
                 grind)
              | exact superpose b11e1425 b11e23
              | exact resolve b11e23 b11e1425
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e1754 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b11e46
                 have i₂ := b11e1712
                 grind)
              | exact superpose b11e1712 b11e46
              | exact resolve b11e46 b11e1712
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e46 b11e1712
            have b11e1767 : False := by grind
            exact b11e1767
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b12e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b12e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e23 : y = (M.op x x) := by grind
            have b12e25 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b12e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e21
              | exact resolve b12e21 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e39 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b12e14 (σ x) (σ x) x
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e14
              | exact resolve b12e14 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e40 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b12e14 x x x
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e14
              | exact resolve b12e14 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e43 : ∀ X0 : G, y = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b12e40 X0
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e40
              | exact resolve b12e40 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e40
            have b12e56 : ∀ X0 : G, y ≠ X0 ∨ (k X0 y) = (M.op y y) := by
              intro X0
              first
              | (have i₁ := b12e17 X0 y
                 have i₂ := b12e43 X0
                 grind)
              | exact superpose b12e43 b12e17
              | (have j0 := b12e17 X0 y
                 grind)
              | (have r₁ := b12e17 y y
                 have r₂ := b12e43 y
                 grind)
              | exact resolve b12e17 b12e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e58 : ∀ X0 : G, y ≠ X0 ∨ y = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b12e56 X0
                 have i₂ := b12e43 y
                 grind)
              | exact superpose b12e43 b12e56
              | (have j0 := b12e56 X0
                 grind)
              | (have r₁ := b12e56 (M.op y X0)
                 have r₂ := b12e43 X0
                 grind)
              | exact resolve b12e56 b12e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e43 b12e56
            have b12e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b12e20 X0 X1
                 have i₂ := b12e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b12e19 b12e20
              | (have j1 := b12e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b12e20 b12e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e122 : y = (k y y) := by
              first
              | (have j0 := b12e58 y
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e58
            have b12e167 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b12e28
                 have i₂ := b12e39 X0
                 grind)
              | exact superpose b12e39 b12e28
              | exact resolve b12e28 b12e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28 b12e39
            have b12e2024 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b12e75 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e75
            have b12e2025 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b12e2024 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e2024
            have b12e20117 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b12e2025 y
                 have i₂ := b12e122
                 grind)
              | exact superpose b12e122 b12e2025
              | (have j0 := b12e2025 y
                 grind)
              | exact resolve b12e2025 b12e122
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e122 b12e2025
            have b12e20129 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b12e20117
            have b12e20136 : False := by grind
            exact b12e20136
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b13e23 : x ≠ (M.op y x) := by grind
              have b13e24 : y = (M.op x x) := by grind
              have b13e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e46 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b13e15 x x x
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e54 : x ≠ (M.op x y) := by
                first
                | (have i₁ := b13e23
                   have i₂ := b13e46 x
                   grind)
                | exact superpose b13e46 b13e23
                | exact resolve b13e23 b13e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e55 : x = (M.op x y) := by
                first
                | (have i₁ := b13e28
                   have i₂ := b13e46 y
                   grind)
                | exact superpose b13e46 b13e28
                | exact resolve b13e28 b13e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e46
              have b13e56 : False := by grind
              exact b13e56
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : y = (M.op x x) := by grind
              have b14e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              have b14e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
              have b14e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X0 X1 X3
                   have i₂ := b14e15 X0 X1 X2
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e44 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b14e15 (σ x) (σ x) x
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e15
                | exact resolve b14e15 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e45 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b14e15 x x x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X2 ∨ (k X2 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e18 X2 (M.op X0 X1)
                   have i₂ := b14e15 X0 X1 X2
                   grind)
                | exact superpose b14e15 b14e18
                | (have j0 := b14e18 X2 (M.op X0 X1)
                   grind)
                | (have r₁ := b14e18 (M.op X0 (M.op X1 X0)) (M.op X0 X1)
                   have r₂ := b14e15 X0 X1 (M.op X0 (M.op X1 X0))
                   grind)
                | exact resolve b14e18 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e58 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b14e18 (σ x) (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e18
                | exact resolve b14e18 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e62 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
                first
                | (have i₁ := b14e58
                   have i₂ := b14e21 x x
                   grind)
                | exact superpose b14e21 b14e58
                | exact resolve b14e58 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e58
              have b14e63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X2 ∨ (M.op X0 (M.op X1 X0)) = (k X2 (M.op X0 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e57 X0 X1 X2
                   have i₂ := b14e15 X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b14e15 b14e57
                | (have j0 := b14e57 X0 X1 X2
                   grind)
                | (have r₁ := b14e57 X0 X1 (M.op (M.op X0 X1) X2)
                   have r₂ := b14e15 X0 X1 X2
                   grind)
                | (have r₁ := b14e57 (M.op X0 X1) X1 (M.op X0 (M.op X1 X0))
                   have r₂ := b14e15 X0 X1 (M.op X1 (M.op X0 X1))
                   grind)
                | exact resolve b14e57 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e57
              have b14e68 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
                intro X0
                grind
              clear b14e30
              have b14e69 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
                intro X0
                first
                | (have i₁ := b14e68 X0
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e68
                | (have j0 := b14e68 X0
                   grind)
                | exact resolve b14e68 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e68
              have b14e74 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b14e69 X0
                   have i₂ := b14e15 (τ X0) (τ X0) (τ X0)
                   grind)
                | exact superpose b14e15 b14e69
                | (have j0 := b14e69 X0
                   grind)
                | exact resolve b14e69 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e69
              have b14e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
              have b14e118 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b14e22
                   have i₂ := b14e44 X0
                   grind)
                | exact superpose b14e44 b14e22
                | exact resolve b14e22 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e119 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
                intro X0
                first
                | (have i₁ := b14e18 (σ y) (σ x)
                   have i₂ := b14e44 X0
                   grind)
                | exact superpose b14e44 b14e18
                | (have j0 := b14e18 (σ y) (σ x)
                   grind)
                | (have r₁ := b14e18 (M.op (σ x) (σ y)) (σ y)
                   have r₂ := b14e44 (M.op (σ x) (σ y))
                   grind)
                | exact resolve b14e18 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e122 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = X0 ∨ (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e20 (σ y) X0
                   have i₂ := b14e44 (σ y)
                   grind)
                | exact superpose b14e44 b14e20
                | (have j0 := b14e20 (σ y) X0
                   grind)
                | exact resolve b14e20 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e134 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b14e119 X0
                   have i₂ := b14e21 y x
                   grind)
                | exact superpose b14e21 b14e119
                | (have j0 := b14e119 X0
                   grind)
                | exact resolve b14e119 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e119
              have b14e137 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (σ y) = (σ (k y x)) := by
                intro X0
                first
                | (have i₁ := b14e134 X0
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e134
                | (have j0 := b14e134 X0
                   grind)
                | exact resolve b14e134 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e134
              have b14e145 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X0 X3) ∨ (M.op X0 X1) = X1 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e40 X0 X0 X2 X3
                   have i₂ := b14e20 X0 X1
                   grind)
                | (have i₁ := b14e40 X0 X1 X2 X3
                   have i₂ := b14e20 X0 (M.op X0 X1)
                   grind)
                | exact superpose b14e20 b14e40
                | (have j1 := b14e20 X1 X0
                   grind)
                | exact resolve b14e40 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e1118 : ∀ X0 X1 : G, (M.op x y) ≠ X1 ∨ (M.op x y) = (k X1 (M.op y X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e63 y X1 x
                   have i₂ := b14e45 (M.op X1 y)
                   grind)
                | exact superpose b14e45 b14e63
                | (have r₁ := b14e63 y X1 (M.op x y)
                   have r₂ := b14e45 (M.op X1 y)
                   grind)
                | exact resolve b14e63 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e63
              have b14e1120 : ∀ X1 : G, (M.op x y) ≠ X1 ∨ (M.op x y) = (k X1 (M.op x y)) := by
                intro X1
                first
                | (have i₁ := b14e1118 x X1
                   have i₂ := b14e45 x
                   grind)
                | exact superpose b14e45 b14e1118
                | (have j0 := b14e1118 x X1
                   grind)
                | (have r₁ := b14e1118 x (M.op y x)
                   have r₂ := b14e45 x
                   grind)
                | exact resolve b14e1118 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1118
              have b14e1818 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b14e84 x x
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e84
                | exact resolve b14e84 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e1921 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b14e84 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e84
              have b14e1922 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b14e1921 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1921
              have b14e1933 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
              clear b14e1818
              have b14e1977 : (σ y) = (σ (k x x)) := by
                first
                | (have r₁ := b14e1933
                   have r₂ := b14e62
                   grind)
                | exact resolve b14e1933 b14e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e62 b14e1933
              have b14e2010 : (k x x) = (τ (σ y)) := by
                first
                | (have i₁ := b14e16 (k x x)
                   have i₂ := b14e1977
                   grind)
                | exact superpose b14e1977 b14e16
                | exact resolve b14e16 b14e1977
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e2011 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (σ y) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b14e21 (k x x) X0
                   have i₂ := b14e1977
                   grind)
                | exact superpose b14e1977 b14e21
                | exact resolve b14e21 b14e1977
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1977
              have b14e2029 : ∀ X0 : G, (σ (k y X0)) = (σ (k (k x x) X0)) := by
                intro X0
                first
                | (have i₁ := b14e2011 X0
                   have i₂ := b14e21 y X0
                   grind)
                | exact superpose b14e21 b14e2011
                | exact resolve b14e2011 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e2011
              have b14e2030 : y = (k x x) := by
                first
                | (have i₁ := b14e2010
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e2010
                | exact resolve b14e2010 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e2010
              have b14e4808 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b14e137 x
                   have i₂ := b14e44 x
                   grind)
                | exact superpose b14e44 b14e137
                | exact resolve b14e137 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e137
              have b14e4832 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
                first
                | (have j0 := b14e1120 (M.op x y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1120
              have b14e18533 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
                first
                | (have i₁ := b14e1922 (M.op x y)
                   have i₂ := b14e4832
                   grind)
                | exact superpose b14e4832 b14e1922
                | (have j0 := b14e1922 (M.op x y)
                   grind)
                | exact resolve b14e1922 b14e4832
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1922 b14e4832
              have b14e18547 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
              clear b14e18533
              have b14e21165 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e40 (σ (M.op x y)) (σ (M.op x y)) x x
                   have i₂ := b14e18547
                   grind)
                | exact superpose b14e18547 b14e40
                | exact resolve b14e40 b14e18547
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e40
              have b14e23126 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
                intro X0
                first
                | (have i₁ := b14e18547
                   have i₂ := b14e21165 (σ (M.op x y)) X0
                   grind)
                | (have i₁ := b14e18547
                   have i₂ := b14e21165 X0 (σ (M.op x y))
                   grind)
                | exact superpose b14e21165 b14e18547
                | exact resolve b14e18547 b14e21165
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e18547 b14e21165
              have b14e55430 : ∀ X0 X1 : G, y = (M.op x X0) ∨ (M.op X1 x) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e24
                   have i₂ := b14e145 x X1 x X0
                   grind)
                | (have i₁ := b14e24
                   have i₂ := b14e145 x X1 X0 x
                   grind)
                | exact superpose b14e145 b14e24
                | (have j1 := b14e145 x X1 x x
                   grind)
                | exact resolve b14e24 b14e145
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e55433 : ∀ X0 X1 : G, y ≠ (M.op x X0) ∨ (M.op X1 x) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e27
                   have i₂ := b14e145 x X1 y X0
                   grind)
                | (have i₁ := b14e27
                   have i₂ := b14e145 x X1 X0 y
                   grind)
                | exact superpose b14e145 b14e27
                | (have j1 := b14e145 x X1 x x
                   grind)
                | (have r₁ := b14e27
                   have r₂ := b14e145 x y x x
                   grind)
                | exact resolve b14e27 b14e145
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e145
              have b14e55461 : ∀ X1 : G, (M.op X1 x) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X1
                first
                | (have j0 := b14e55430 x X1
                   have j1 := b14e55433 x X1
                   grind)
                | (have r₁ := b14e55430 x X1
                   have r₂ := b14e55433 x X1
                   grind)
                | (have r₁ := b14e55430 x y
                   have r₂ := b14e55433 y X1
                   grind)
                | exact resolve b14e55430 b14e55433
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e55430 b14e55433
              have b14e55520 : (σ (k y x)) = (σ (M.op (k x x) x)) ∨ (k x x) = (M.op x (k x x)) := by
                first
                | (have i₁ := b14e2029 x
                   have i₂ := b14e55461 (k x x)
                   grind)
                | exact superpose b14e55461 b14e2029
                | (have j1 := b14e55461 (k x x)
                   grind)
                | exact resolve b14e2029 b14e55461
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e2029 b14e55461
              have b14e55532 : (σ (k y x)) = (σ (M.op y x)) ∨ (k x x) = (M.op x (k x x)) := by
                first
                | (have i₁ := b14e55520
                   have i₂ := b14e2030
                   grind)
                | exact superpose b14e2030 b14e55520
                | exact resolve b14e55520 b14e2030
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e55520
              have b14e55533 : (σ (M.op x y)) = (σ (k y x)) ∨ (k x x) = (M.op x (k x x)) := by
                first
                | (have i₁ := b14e55532
                   have i₂ := b14e45 x
                   grind)
                | exact superpose b14e45 b14e55532
                | exact resolve b14e55532 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e55532
              have b14e55534 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ (k y x)) := by
                first
                | (have i₁ := b14e55533
                   have i₂ := b14e2030
                   grind)
                | exact superpose b14e2030 b14e55533
                | exact resolve b14e55533 b14e2030
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e2030 b14e55533
              have b14e55535 : (σ (M.op x y)) = (σ (k y x)) := by
                first
                | (have r₁ := b14e55534
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e55534 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e55534
              have b14e133983 : (σ y) = (M.op (σ y) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (M.op (τ (σ y)) (τ (σ y)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ y)) (τ (σ y)))) ∨ (σ y) = (M.op (σ (M.op (τ (σ y)) (τ (σ y)))) (σ y)) := by
                first
                | (have i₁ := b14e74 (σ y)
                   have i₂ := b14e122 (σ (M.op (τ (σ y)) (τ (σ y))))
                   grind)
                | exact superpose b14e122 b14e74
                | (have j0 := b14e74 (σ y)
                   have j1 := b14e122 (σ (M.op (τ (σ y)) (τ (σ y))))
                   grind)
                | exact resolve b14e74 b14e122
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e74 b14e122
              have b14e134205 : (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (M.op (τ (σ y)) (τ (σ y)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ y)) (τ (σ y)))) ∨ (σ y) = (M.op (σ (M.op (τ (σ y)) (τ (σ y)))) (σ y)) := by
                first
                | (have i₁ := b14e133983
                   have i₂ := b14e44 (σ (M.op (τ (σ y)) (τ (σ y))))
                   grind)
                | exact superpose b14e44 b14e133983
                | exact resolve b14e133983 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e44 b14e133983
              have b14e134258 : y = (M.op y (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ y)) (τ (σ y)))) ∨ (σ y) = (M.op (σ (M.op (τ (σ y)) (τ (σ y)))) (σ y)) := by
                first
                | (have i₁ := b14e134205
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e134205
                | exact resolve b14e134205 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e134205
              have b14e134273 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ y)) (τ (σ y)))) ∨ (σ y) = (M.op (σ (M.op (τ (σ y)) (τ (σ y)))) (σ y)) := by
                first
                | (have i₁ := b14e134258
                   have i₂ := b14e45 (M.op y y)
                   grind)
                | exact superpose b14e45 b14e134258
                | exact resolve b14e134258 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e134258
              have b14e134278 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ y)) (τ (σ y)))) ∨ (σ y) = (M.op (σ (M.op (τ (σ y)) (τ (σ y)))) (σ y)) := by
                first
                | (have r₁ := b14e134273
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e134273 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e134273
              have b14e134281 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op (τ (σ y)) (τ (σ y)))) (σ y)) := by
                first
                | (have i₁ := b14e134278
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e134278
                | exact resolve b14e134278 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e134278
              have b14e134284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op (τ (σ y)) (τ (σ y)))) (σ y)) := by
                first
                | (have i₁ := b14e134281
                   have i₂ := b14e45 y
                   grind)
                | exact superpose b14e45 b14e134281
                | exact resolve b14e134281 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e134281
              have b14e134286 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op (τ (σ y)) (τ (σ y)))) (σ y)) := by
                first
                | (have r₁ := b14e134284
                   have r₂ := b14e22
                   grind)
                | exact resolve b14e134284 b14e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e134284
              have b14e134288 : (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e134286
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e134286
                | exact resolve b14e134286 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e134286
              have b14e134290 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e134288
                   have i₂ := b14e45 y
                   grind)
                | exact superpose b14e45 b14e134288
                | exact resolve b14e134288 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e45 b14e134288
              have b14e134292 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
                first
                | (have i₁ := b14e134290
                   have i₂ := b14e23126 (σ y)
                   grind)
                | exact superpose b14e23126 b14e134290
                | exact resolve b14e134290 b14e23126
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e134290
              have b14e134318 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ y) := by
                first
                | (have i₁ := b14e4808
                   have i₂ := b14e134292
                   grind)
                | exact superpose b14e134292 b14e4808
                | (have r₁ := b14e4808
                   have r₂ := b14e134292
                   grind)
                | exact resolve b14e4808 b14e134292
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e4808 b14e134292
              have b14e134445 : (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ y) := by grind
              clear b14e134318
              have b14e134521 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
                first
                | (have i₁ := b14e134445
                   have i₂ := b14e55535
                   grind)
                | exact superpose b14e55535 b14e134445
                | exact resolve b14e134445 b14e55535
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e55535 b14e134445
              have b14e134522 : (σ (M.op x y)) = (σ y) := by grind
              clear b14e134521
              have b14e136994 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b14e118 X0
                   have i₂ := b14e134522
                   grind)
                | exact superpose b14e134522 b14e118
                | exact resolve b14e118 b14e134522
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e118
              have b14e137000 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b14e23126 X0
                   have i₂ := b14e134522
                   grind)
                | exact superpose b14e134522 b14e23126
                | exact resolve b14e23126 b14e134522
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e23126 b14e134522
              have b14e137047 : False := by grind
              exact b14e137047
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b15e22 : x ≠ (M.op y x) := by grind
            have b15e23 : y = (M.op x x) := by grind
            have b15e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e21
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e21
              | exact resolve b15e21 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
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
            have b15e36 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b15e14 x x x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e42 : ∀ X0 : G, y = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b15e36 X0
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e36
              | exact resolve b15e36 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e36
            have b15e47 : x ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e42 x
                 grind)
              | exact superpose b15e42 b15e22
              | exact resolve b15e22 b15e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e42
            have b15e59 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b15e61 : x = (k x y) := by
              first
              | (have r₁ := b15e59
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e59 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e59
            have b15e72 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e14 X0 X0 X2
                 have i₂ := b15e19 X0 X1
                 grind)
              | (have i₁ := b15e14 X0 X1 X2
                 have i₂ := b15e19 X0 (M.op X1 X0)
                 grind)
              | exact superpose b15e19 b15e14
              | (have j1 := b15e19 X1 X0
                 grind)
              | exact resolve b15e14 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e74 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b15e25
                 have i₂ := b15e19 (σ x) X0
                 grind)
              | (have i₁ := b15e25
                 have i₂ := b15e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b15e19 b15e25
              | (have j1 := b15e19 (σ x) X0
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 (σ x) (σ y)
                 grind)
              | exact resolve b15e25 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e2045 : ∀ X0 : G, y = (M.op x X0) ∨ y = (k x x) ∨ x = y := by
              intro X0
              first
              | (have i₁ := b15e72 x x x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e72
              | exact resolve b15e72 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e2203 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1
              first
              | (have j0 := b15e72 X0 X0 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e72
            have b15e2209 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
              intro X0 X1
              first
              | (have j0 := b15e2203 X0 X1
                 have j1 := b15e17 X0 X0
                 grind)
              | (have r₁ := b15e2203 X0 X1
                 have r₂ := b15e17 X0 X0
                 grind)
              | exact resolve b15e2203 b15e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2203
            have b15e2277 : ∀ X0 : G, y = (M.op x X0) ∨ y = (k x x) := by
              intro X0
              first
              | (have j0 := b15e2045 X0
                 grind)
              | (have r₁ := b15e2045 X0
                 have r₂ := b15e47
                 grind)
              | exact resolve b15e2045 b15e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2045
            have b15e2476 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b15e74 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e74
            have b15e2477 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b15e2476
                 have r₂ := b15e24
                 grind)
              | exact resolve b15e2476 b15e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2476
            have b15e2478 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b15e2477
                 have i₂ := b15e20 x y
                 grind)
              | exact superpose b15e20 b15e2477
              | exact resolve b15e2477 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2477
            have b15e2479 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e2478
                 have i₂ := b15e61
                 grind)
              | exact superpose b15e61 b15e2478
              | exact resolve b15e2478 b15e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e61 b15e2478
            have b15e2482 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b15e28
                 have i₂ := b15e2479
                 grind)
              | exact superpose b15e2479 b15e28
              | exact resolve b15e28 b15e2479
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28
            have b15e2488 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
              intro X0 X1
              first
              | (have i₁ := b15e34 (σ x) (σ y) x x
                 have i₂ := b15e2479
                 grind)
              | exact superpose b15e2479 b15e34
              | exact resolve b15e34 b15e2479
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e34
            have b15e2501 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b15e2209 (σ x) (σ y)
                 have i₂ := b15e2479
                 grind)
              | exact superpose b15e2479 b15e2209
              | (have j0 := b15e2209 (σ x) x
                 grind)
              | (have r₁ := b15e2209 (σ x) (σ y)
                 have r₂ := b15e2479
                 grind)
              | exact resolve b15e2209 b15e2479
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2209
            have b15e2502 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
            clear b15e2501
            have b15e2503 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
              first
              | (have i₁ := b15e2502
                 have i₂ := b15e20 x x
                 grind)
              | exact superpose b15e20 b15e2502
              | exact resolve b15e2502 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2502
            have b15e2964 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b15e2479
                 have i₂ := b15e2488 (σ y) X0
                 grind)
              | (have i₁ := b15e2479
                 have i₂ := b15e2488 X0 (σ y)
                 grind)
              | exact superpose b15e2488 b15e2479
              | exact resolve b15e2479 b15e2488
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2479 b15e2488
            have b15e3686 : (σ x) = (σ (k x x)) := by
              first
              | (have i₁ := b15e2964 (σ x)
                 have i₂ := b15e2503
                 grind)
              | exact superpose b15e2503 b15e2964
              | exact resolve b15e2964 b15e2503
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2503 b15e2964
            have b15e3868 : ∀ X0 : G, (σ x) = (σ y) ∨ y = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b15e3686
                 have i₂ := b15e2277 X0
                 grind)
              | exact superpose b15e2277 b15e3686
              | (have j1 := b15e2277 X0
                 grind)
              | exact resolve b15e3686 b15e2277
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2277
            have b15e3873 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b15e3686
                 have i₂ := b15e19 x x
                 grind)
              | exact superpose b15e19 b15e3686
              | (have j1 := b15e19 x x
                 grind)
              | exact resolve b15e3686 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e3686
            have b15e3884 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
            clear b15e3873
            have b15e3895 : (σ x) = (σ y) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b15e3884
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e3884
              | exact resolve b15e3884 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e3884
            have b15e3900 : ∀ X0 : G, y = (M.op x X0) := by
              intro X0
              first
              | (have j0 := b15e3868 X0
                 grind)
              | (have r₁ := b15e3868 X0
                 have r₂ := b15e2482
                 grind)
              | exact resolve b15e3868 b15e2482
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e3868
            have b15e3904 : x = (M.op x x) := by
              first
              | (have r₁ := b15e3895
                 have r₂ := b15e2482
                 grind)
              | exact resolve b15e3895 b15e2482
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2482 b15e3895
            have b15e3911 : x = y := by
              first
              | (have i₁ := b15e3904
                 have i₂ := b15e3900 x
                 grind)
              | exact superpose b15e3900 b15e3904
              | exact resolve b15e3904 b15e3900
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e3900 b15e3904
            have b15e3918 : False := by grind
            exact b15e3918
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b16e23 : x ≠ (M.op y x) := by grind
              have b16e24 : y = (M.op x x) := by grind
              have b16e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e44 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b16e15 x x x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e52 : x ≠ (M.op x y) := by
                first
                | (have i₁ := b16e23
                   have i₂ := b16e44 x
                   grind)
                | exact superpose b16e44 b16e23
                | exact resolve b16e23 b16e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e53 : x = (M.op x y) := by
                first
                | (have i₁ := b16e28
                   have i₂ := b16e44 y
                   grind)
                | exact superpose b16e44 b16e28
                | exact resolve b16e28 b16e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e44
              have b16e54 : False := by grind
              exact b16e54
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b17e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : x ≠ (M.op y x) := by grind
              have b17e24 : y = (M.op x x) := by grind
              have b17e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 X0 X1 X3
                   have i₂ := b17e15 X0 X1 X2
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e56 : x ≠ y ∨ y = (k x x) := by
                first
                | (have i₁ := b17e18 x x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e18
                | exact resolve b17e18 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e61 : x = (k x y) ∨ x = (M.op y x) := by grind
              have b17e66 : x = (k x y) := by
                first
                | (have r₁ := b17e61
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e61 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e61
              have b17e82 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X0 X0 X2
                   have i₂ := b17e20 X0 X1
                   grind)
                | (have i₁ := b17e15 X0 X1 X2
                   have i₂ := b17e20 X0 (M.op X1 X0)
                   grind)
                | exact superpose b17e20 b17e15
                | (have j1 := b17e20 X1 X0
                   grind)
                | exact resolve b17e15 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e84 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
              have b17e1201 : ∀ X0 : G, y = (M.op x X0) ∨ y = (k x x) ∨ x = y := by
                intro X0
                first
                | (have i₁ := b17e82 x x x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e82
                | exact resolve b17e82 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e1331 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
                intro X0 X1
                first
                | (have j0 := b17e82 X0 X0 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e82
              have b17e1335 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
                intro X0 X1
                first
                | (have j0 := b17e1331 X0 X1
                   have j1 := b17e18 X0 X0
                   grind)
                | (have r₁ := b17e1331 X0 X1
                   have r₂ := b17e18 X0 X0
                   grind)
                | exact resolve b17e1331 b17e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1331
              have b17e1366 : ∀ X0 : G, y = (M.op x X0) ∨ y = (k x x) := by
                intro X0
                first
                | (have j0 := b17e1201 X0
                   grind)
                | (have r₁ := b17e1201 X0
                   have r₂ := b17e56
                   grind)
                | exact resolve b17e1201 b17e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e56 b17e1201
              have b17e1488 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b17e84 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e84
              have b17e1489 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e1488
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e1488 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1488
              have b17e1490 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e1489
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e1489
                | exact resolve b17e1489 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1489
              have b17e1491 : (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b17e1490
                   have i₂ := b17e66
                   grind)
                | exact superpose b17e66 b17e1490
                | exact resolve b17e1490 b17e66
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e66 b17e1490
              have b17e1500 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e39 (σ x) (σ y) x x
                   have i₂ := b17e1491
                   grind)
                | exact superpose b17e1491 b17e39
                | exact resolve b17e39 b17e1491
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e39
              have b17e1511 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b17e1335 (σ x) (σ y)
                   have i₂ := b17e1491
                   grind)
                | exact superpose b17e1491 b17e1335
                | (have j0 := b17e1335 (σ x) x
                   grind)
                | (have r₁ := b17e1335 (σ x) (σ y)
                   have r₂ := b17e1491
                   grind)
                | exact resolve b17e1335 b17e1491
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1335
              have b17e1512 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
              clear b17e1511
              have b17e1513 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
                first
                | (have i₁ := b17e1512
                   have i₂ := b17e21 x x
                   grind)
                | exact superpose b17e21 b17e1512
                | exact resolve b17e1512 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1512
              have b17e1899 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b17e26
                   have i₂ := b17e1500 (σ x) X0
                   grind)
                | (have i₁ := b17e26
                   have i₂ := b17e1500 X0 (σ x)
                   grind)
                | exact superpose b17e1500 b17e26
                | exact resolve b17e26 b17e1500
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e1900 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b17e1491
                   have i₂ := b17e1500 (σ y) X0
                   grind)
                | (have i₁ := b17e1491
                   have i₂ := b17e1500 X0 (σ y)
                   grind)
                | exact superpose b17e1500 b17e1491
                | exact resolve b17e1491 b17e1500
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1491 b17e1500
              have b17e1903 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b17e1899 x
                   have i₂ := b17e1900 x
                   grind)
                | exact superpose b17e1900 b17e1899
                | exact resolve b17e1899 b17e1900
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1899
              have b17e2605 : (σ x) = (σ (k x x)) := by
                first
                | (have i₁ := b17e1900 (σ x)
                   have i₂ := b17e1513
                   grind)
                | exact superpose b17e1513 b17e1900
                | exact resolve b17e1900 b17e1513
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1513 b17e1900
              have b17e2696 : ∀ X0 : G, (σ x) = (σ y) ∨ y = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b17e2605
                   have i₂ := b17e1366 X0
                   grind)
                | exact superpose b17e1366 b17e2605
                | (have j1 := b17e1366 X0
                   grind)
                | exact resolve b17e2605 b17e1366
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1366
              have b17e2701 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b17e2605
                   have i₂ := b17e20 x x
                   grind)
                | exact superpose b17e20 b17e2605
                | (have j1 := b17e20 x x
                   grind)
                | exact resolve b17e2605 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2605
              have b17e2712 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
              clear b17e2701
              have b17e2723 : (σ x) = (σ y) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b17e2712
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e2712
                | exact resolve b17e2712 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2712
              have b17e2728 : ∀ X0 : G, y = (M.op x X0) := by
                intro X0
                first
                | (have j0 := b17e2696 X0
                   grind)
                | (have r₁ := b17e2696 X0
                   have r₂ := b17e1903
                   grind)
                | exact resolve b17e2696 b17e1903
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2696
              have b17e2732 : x = (M.op x x) := by
                first
                | (have r₁ := b17e2723
                   have r₂ := b17e1903
                   grind)
                | exact resolve b17e2723 b17e1903
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2723
              have b17e2739 : x = y := by
                first
                | (have i₁ := b17e2732
                   have i₂ := b17e2728 x
                   grind)
                | exact superpose b17e2728 b17e2732
                | exact resolve b17e2732 b17e2728
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2728 b17e2732
              have b17e2850 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b17e1903
                   have i₂ := b17e2739
                   grind)
                | exact superpose b17e2739 b17e1903
                | exact resolve b17e1903 b17e2739
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1903 b17e2739
              have b17e2851 : False := by grind
              exact b17e2851
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b18e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b18e21 : x ≠ (M.op y x) := by grind
          have b18e22 : y ≠ (M.op x x) := by grind
          have b18e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          have b18e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b18e20
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e20
            | exact resolve b18e20 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 X1)) X3) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 X2 (M.op X0 X1) X3
               have i₂ := b18e13 X0 X1 X2
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 X0 X1 X3
               have i₂ := b18e13 X0 X1 X2
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 (M.op X0 X1) X2 X3
               have i₂ := b18e13 X0 X1 X2
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e40 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b18e13 (σ y) (σ x) X0
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e13
            | exact resolve b18e13 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e43 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e39 X0 X1 x X3
               have i₂ := b18e13 X0 X1 (M.op x (M.op X0 X1))
               grind)
            | exact superpose b18e13 b18e39
            | exact resolve b18e39 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e39
          have b18e61 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
          have b18e62 : y ≠ y ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b18e16 y x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e16
            | (have j0 := b18e16 y x
               grind)
            | (have r₁ := b18e16 y x
               have r₂ := b18e24
               grind)
            | exact resolve b18e16 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e65 : (M.op x x) = (k y x) := by grind
          clear b18e62
          have b18e66 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear b18e61
          have b18e68 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b18e66
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e66
            | exact resolve b18e66 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e66
          have b18e111 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X0 X0 X2
               have i₂ := b18e18 X0 X1
               grind)
            | (have i₁ := b18e13 X0 X1 X2
               have i₂ := b18e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b18e18 b18e13
            | (have j1 := b18e18 X1 X0
               grind)
            | exact resolve b18e13 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e153 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e36 (σ y) (σ x) x x
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e36
            | exact resolve b18e36 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e154 : ∀ X0 X1 : G, (M.op (σ (k x y)) X0) = (M.op (σ (k x y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e36 (σ y) (σ y) x x
               have i₂ := b18e68
               grind)
            | exact superpose b18e68 b18e36
            | exact resolve b18e36 b18e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36
          have b18e236 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b18e26
               have i₂ := b18e153 (σ y) X0
               grind)
            | (have i₁ := b18e26
               have i₂ := b18e153 X0 (σ y)
               grind)
            | exact superpose b18e153 b18e26
            | exact resolve b18e26 b18e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e26
          have b18e268 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b18e236 x
               have i₂ := b18e40 x
               grind)
            | exact superpose b18e40 b18e236
            | exact resolve b18e236 b18e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e40
          have b18e1586 : ∀ X0 : G, y ≠ (M.op x X0) ∨ (M.op x x) = (k x x) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b18e22
               have i₂ := b18e111 x x X0
               grind)
            | (have i₁ := b18e22
               have i₂ := b18e111 x x x
               grind)
            | exact superpose b18e111 b18e22
            | (have j1 := b18e111 x x x
               grind)
            | exact resolve b18e22 b18e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e1651 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b18e111 X0 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e111
          have b18e1655 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b18e1651 X0 X1
               have j1 := b18e16 X0 X0
               grind)
            | (have r₁ := b18e1651 X0 X1
               have r₂ := b18e16 X0 X0
               grind)
            | exact resolve b18e1651 b18e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1651
          have b18e1661 : ∀ X0 : G, y ≠ (M.op x X0) ∨ (M.op x x) = (k x x) := by
            intro X0
            first
            | (have j0 := b18e1586 X0
               have j1 := b18e16 x x
               grind)
            | (have r₁ := b18e1586 X0
               have r₂ := b18e16 x x
               grind)
            | exact resolve b18e1586 b18e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1586
          have b18e1875 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b18e268
               have i₂ := b18e153 (σ y) X0
               grind)
            | (have i₁ := b18e268
               have i₂ := b18e153 X0 (σ y)
               grind)
            | exact superpose b18e153 b18e268
            | exact resolve b18e268 b18e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e153 b18e268
          have b18e2859 : y ≠ y ∨ (M.op x x) = (k x x) := by
            first
            | (have i₁ := b18e1661 y
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e1661
            | (have r₁ := b18e1661 y
               have r₂ := b18e24
               grind)
            | exact resolve b18e1661 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1661
          have b18e2868 : (M.op x x) = (k x x) := by grind
          clear b18e2859
          have b18e3597 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            intro X0 X1
            first
            | (have i₁ := b18e154 X0 X1
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e154
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e154 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e154
          have b18e3728 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) ∨ x = (M.op y x) := by
            intro X0 X1
            first
            | (have j0 := b18e3597 X0 X1
               grind)
            | (have r₁ := b18e3597 X0 X1
               have r₂ := b18e22
               grind)
            | exact resolve b18e3597 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3597
          have b18e3742 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) := by
            intro X0 X1
            first
            | (have j0 := b18e3728 X0 X1
               grind)
            | (have r₁ := b18e3728 X0 X1
               have r₂ := b18e21
               grind)
            | exact resolve b18e3728 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3728
          have b18e3747 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e3742 X0 X1
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e3742
            | exact resolve b18e3742 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3742
          have b18e3827 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
            intro X0
            grind
          have b18e3850 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b18e1875 x
               have i₂ := b18e3747 (M.op (σ x) x) X0
               grind)
            | (have i₁ := b18e1875 x
               have i₂ := b18e3747 X0 (M.op (σ x) x)
               grind)
            | exact superpose b18e3747 b18e1875
            | exact resolve b18e1875 b18e3747
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1875
          have b18e3853 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) X0) X2) := by
            intro X0 X2
            first
            | (have i₁ := b18e43 (σ y) x x
               have i₂ := b18e3747 (M.op x (σ y)) x
               grind)
            | (have i₁ := b18e43 (σ y) x x
               have i₂ := b18e3747 X0 (M.op x (σ y))
               grind)
            | exact superpose b18e3747 b18e43
            | exact resolve b18e43 b18e3747
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e43
          have b18e3857 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ y) X0) X3) = (M.op (σ y) (M.op X1 (M.op X2 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e34 X1 X2 (σ y) X3
               have i₂ := b18e3747 (M.op X1 X2) X0
               grind)
            | (have i₁ := b18e34 X1 X2 (σ y) X3
               have i₂ := b18e3747 X0 (M.op X1 X2)
               grind)
            | exact superpose b18e3747 b18e34
            | exact resolve b18e34 b18e3747
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e34
          have b18e3865 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b18e23
               have i₂ := b18e3747 (σ x) X0
               grind)
            | (have i₁ := b18e23
               have i₂ := b18e3747 X0 (σ x)
               grind)
            | exact superpose b18e3747 b18e23
            | exact resolve b18e23 b18e3747
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e3866 : ∀ X0 : G, (σ (k x y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b18e68
               have i₂ := b18e3747 (σ y) X0
               grind)
            | (have i₁ := b18e68
               have i₂ := b18e3747 X0 (σ y)
               grind)
            | exact superpose b18e3747 b18e68
            | exact resolve b18e68 b18e3747
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e68 b18e3747
          have b18e3876 : ∀ X0 X3 : G, (σ (k x y)) = (M.op (M.op (σ y) X0) X3) := by
            intro X0 X3
            first
            | (have i₁ := b18e3857 X0 x x X3
               have i₂ := b18e3866 (M.op x (M.op x x))
               grind)
            | exact superpose b18e3866 b18e3857
            | exact resolve b18e3857 b18e3866
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3857
          have b18e3879 : ∀ X2 : G, (σ x) = (M.op (σ x) X2) := by
            intro X2
            first
            | (have i₁ := b18e3853 x X2
               have i₂ := b18e3865 x
               grind)
            | exact superpose b18e3865 b18e3853
            | exact resolve b18e3853 b18e3865
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3853
          have b18e3882 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b18e3850 x
               have i₂ := b18e3865 x
               grind)
            | exact superpose b18e3865 b18e3850
            | exact resolve b18e3850 b18e3865
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3850
          have b18e3901 : ∀ X0 : G, (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e3827 X0
               have i₂ := b18e3865 X0
               grind)
            | exact superpose b18e3865 b18e3827
            | (have j0 := b18e3827 X0
               grind)
            | exact resolve b18e3827 b18e3865
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3827
          have b18e3965 : ∀ X3 : G, (σ (k x y)) = (M.op (σ x) X3) := by
            intro X3
            first
            | (have i₁ := b18e3876 x X3
               have i₂ := b18e3865 x
               grind)
            | exact superpose b18e3865 b18e3876
            | exact resolve b18e3876 b18e3865
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3865 b18e3876
          have b18e3979 : ∀ X0 : G, (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e3901 X0
               have i₂ := b18e19 y x
               grind)
            | exact superpose b18e19 b18e3901
            | (have j0 := b18e3901 X0
               grind)
            | exact resolve b18e3901 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3901
          have b18e4019 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b18e3965 x
               have i₂ := b18e3879 x
               grind)
            | exact superpose b18e3879 b18e3965
            | exact resolve b18e3965 b18e3879
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3965
          have b18e4027 : ∀ X0 : G, (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e3979 X0
               have i₂ := b18e65
               grind)
            | exact superpose b18e65 b18e3979
            | (have j0 := b18e3979 X0
               grind)
            | exact resolve b18e3979 b18e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e65 b18e3979
          have b18e4041 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (σ (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b18e4027 X0
               have i₂ := b18e13 (σ y) X0 (σ y)
               grind)
            | exact superpose b18e13 b18e4027
            | exact resolve b18e4027 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e4027
          have b18e4048 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b18e4041 x
               have i₂ := b18e3866 (M.op x (σ y))
               grind)
            | exact superpose b18e3866 b18e4041
            | exact resolve b18e4041 b18e3866
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3866 b18e4041
          have b18e4051 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b18e4048
               have i₂ := b18e4019
               grind)
            | exact superpose b18e4019 b18e4048
            | exact resolve b18e4048 b18e4019
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e4019 b18e4048
          have b18e4053 : (σ y) = (σ (M.op x x)) := by
            first
            | (have r₁ := b18e4051
               have r₂ := b18e3882
               grind)
            | exact resolve b18e4051 b18e3882
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3882 b18e4051
          have b18e5239 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b18e1655 (σ x) x
               have i₂ := b18e3879 x
               grind)
            | exact superpose b18e3879 b18e1655
            | (have j0 := b18e1655 (σ x) x
               grind)
            | (have r₁ := b18e1655 (σ x) x
               have r₂ := b18e3879 x
               grind)
            | exact resolve b18e1655 b18e3879
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1655 b18e3879
          have b18e5266 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
          clear b18e5239
          have b18e5279 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
            first
            | (have i₁ := b18e5266
               have i₂ := b18e19 x x
               grind)
            | exact superpose b18e19 b18e5266
            | exact resolve b18e5266 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e5266
          have b18e5300 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b18e5279
               have i₂ := b18e2868
               grind)
            | exact superpose b18e2868 b18e5279
            | exact resolve b18e5279 b18e2868
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e2868 b18e5279
          have b18e5303 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b18e5300
               have i₂ := b18e4053
               grind)
            | exact superpose b18e4053 b18e5300
            | exact resolve b18e5300 b18e4053
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e4053 b18e5300
          have b18e5305 : False := by grind
          exact b18e5305
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : x ≠ (M.op y x) := by grind
            have b19e23 : y ≠ (M.op x x) := by grind
            have b19e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b19e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e39 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b19e14 y y x
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e14
              | exact resolve b19e14 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e44 : ∀ X0 : G, x ≠ (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b19e22
                 have i₂ := b19e39 X0
                 grind)
              | exact superpose b19e39 b19e22
              | exact resolve b19e22 b19e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e39
            have b19e54 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
            have b19e58 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
            clear b19e54
            have b19e59 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b19e58
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e58
              | exact resolve b19e58 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e58
            have b19e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
            have b19e135 : (σ y) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b19e17 (σ y) (σ y)
                 have i₂ := b19e59
                 grind)
              | exact superpose b19e59 b19e17
              | exact resolve b19e17 b19e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e138 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b19e135
                 have i₂ := b19e20 y y
                 grind)
              | exact superpose b19e20 b19e135
              | exact resolve b19e135 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e135
            have b19e1773 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b19e70 y y
                 have i₂ := b19e59
                 grind)
              | exact superpose b19e59 b19e70
              | exact resolve b19e70 b19e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e59 b19e70
            have b19e1877 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k y y)) := by grind
            clear b19e1773
            have b19e1900 : (σ (k x y)) = (σ (k y y)) := by
              first
              | (have r₁ := b19e1877
                 have r₂ := b19e138
                 grind)
              | exact resolve b19e1877 b19e138
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e138 b19e1877
            have b19e1922 : (k y y) = (τ (σ (k x y))) := by
              first
              | (have i₁ := b19e15 (k y y)
                 have i₂ := b19e1900
                 grind)
              | exact superpose b19e1900 b19e15
              | exact resolve b19e15 b19e1900
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1900
            have b19e1942 : (k y y) = (k x y) := by
              first
              | (have i₁ := b19e1922
                 have i₂ := b19e15 (k x y)
                 grind)
              | exact superpose b19e15 b19e1922
              | exact resolve b19e1922 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1922
            have b19e2059 : (M.op y y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e19 y y
                 have i₂ := b19e1942
                 grind)
              | exact superpose b19e1942 b19e19
              | (have j0 := b19e19 y y
                 grind)
              | exact resolve b19e19 b19e1942
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1942
            have b19e2060 : (M.op y y) = (k x y) ∨ y = (M.op y y) := by grind
            clear b19e2059
            have b19e2062 : x = (k x y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e2060
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e2060
              | exact resolve b19e2060 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2060
            have b19e2072 : x = (k x y) ∨ x = y := by
              first
              | (have i₁ := b19e2062
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e2062
              | exact resolve b19e2062 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2062
            have b19e2336 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ x = y := by
              first
              | (have i₁ := b19e19 x y
                 have i₂ := b19e2072
                 grind)
              | exact superpose b19e2072 b19e19
              | (have j0 := b19e19 x y
                 grind)
              | exact resolve b19e19 b19e2072
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2072
            have b19e2337 : y = (M.op x x) ∨ x = (M.op y x) ∨ x = y := by
              first
              | (have r₁ := b19e2336
                 have r₂ := b19e44 y
                 grind)
              | exact resolve b19e2336 b19e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2336
            have b19e2346 : x = (M.op y x) ∨ x = y := by
              first
              | (have r₁ := b19e2337
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e2337 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2337
            have b19e2354 : x = y := by
              first
              | (have r₁ := b19e2346
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e2346 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2346
            have b19e2498 : x = (M.op x x) := by
              first
              | (have i₁ := b19e26
                 have i₂ := b19e2354
                 grind)
              | exact superpose b19e2354 b19e26
              | exact resolve b19e26 b19e2354
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2354
            have b19e2520 : False := by grind
            exact b19e2520
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b20e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b20e22 : x ≠ (M.op y x) := by grind
            have b20e23 : y ≠ (M.op x x) := by grind
            have b20e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b20e25 : y ≠ (M.op x y) := by grind
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
            have b20e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 X0 X1 X3
                 have i₂ := b20e14 X0 X1 X2
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e35 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b20e14 (σ y) (σ x) X0
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e14
              | exact resolve b20e14 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e44 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
            have b20e45 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
            have b20e46 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X0 X0) = (k (M.op X1 X0) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e17 (M.op X1 X0) X0
                 have i₂ := b20e14 X0 X1 X2
                 grind)
              | exact superpose b20e14 b20e17
              | (have j0 := b20e17 (M.op X1 X0) X0
                 grind)
              | (have r₁ := b20e17 (M.op X0 (M.op X1 X0)) (M.op X0 X1)
                 have r₂ := b20e14 X0 X1 (M.op X0 (M.op X1 X0))
                 grind)
              | exact resolve b20e17 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e47 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X2 ∨ (k X2 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e17 X2 (M.op X0 X1)
                 have i₂ := b20e14 X0 X1 X2
                 grind)
              | exact superpose b20e14 b20e17
              | (have j0 := b20e17 X2 (M.op X0 X1)
                 grind)
              | (have r₁ := b20e17 (M.op X0 (M.op X1 X0)) (M.op X0 X1)
                 have r₂ := b20e14 X0 X1 (M.op X0 (M.op X1 X0))
                 grind)
              | exact resolve b20e17 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e48 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
            clear b20e45
            have b20e49 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X2 ∨ (M.op X0 (M.op X1 X0)) = (k X2 (M.op X0 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e47 X0 X1 X2
                 have i₂ := b20e14 X0 X1 (M.op X0 X1)
                 grind)
              | exact superpose b20e14 b20e47
              | (have j0 := b20e47 X0 X1 X2
                 grind)
              | (have r₁ := b20e47 X0 X1 (M.op (M.op X0 X1) X2)
                 have r₂ := b20e14 X0 X1 X2
                 grind)
              | (have r₁ := b20e47 (M.op X0 X1) X1 (M.op X0 (M.op X1 X0))
                 have r₂ := b20e14 X0 X1 (M.op X1 (M.op X0 X1))
                 grind)
              | exact resolve b20e47 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e47
            have b20e50 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b20e48
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e48
              | exact resolve b20e48 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e48
            have b20e65 : (σ y) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b20e17 (σ y) (σ y)
                 have i₂ := b20e50
                 grind)
              | exact superpose b20e50 b20e17
              | exact resolve b20e17 b20e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e67 : ∀ X0 : G, (M.op (σ y) (σ (k x y))) = (M.op (σ (k x y)) X0) := by
              intro X0
              first
              | (have i₁ := b20e14 (σ y) (σ y) x
                 have i₂ := b20e50
                 grind)
              | exact superpose b20e50 b20e14
              | exact resolve b20e14 b20e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e68 : (σ y) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (k y y)) := by
              first
              | (have i₁ := b20e65
                 have i₂ := b20e20 y y
                 grind)
              | exact superpose b20e20 b20e65
              | exact resolve b20e65 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e65
            have b20e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b20e20 X0 X1
                 have i₂ := b20e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b20e19 b20e20
              | (have j1 := b20e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b20e20 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e81 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e14 X0 X0 X2
                 have i₂ := b20e19 X0 X1
                 grind)
              | (have i₁ := b20e14 X0 X1 X2
                 have i₂ := b20e19 X0 (M.op X1 X0)
                 grind)
              | exact superpose b20e19 b20e14
              | (have j1 := b20e19 X1 X0
                 grind)
              | exact resolve b20e14 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e99 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
              intro X0 X1
              first
              | (have i₁ := b20e33 (σ y) (σ x) x x
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e33
              | exact resolve b20e33 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e100 : ∀ X0 X1 : G, (M.op (σ (k x y)) X0) = (M.op (σ (k x y)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b20e33 (σ y) (σ y) x x
                 have i₂ := b20e50
                 grind)
              | exact superpose b20e50 b20e33
              | exact resolve b20e33 b20e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e154 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b20e21
                 have i₂ := b20e99 (σ y) X0
                 grind)
              | (have i₁ := b20e21
                 have i₂ := b20e99 X0 (σ y)
                 grind)
              | exact superpose b20e99 b20e21
              | exact resolve b20e21 b20e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e186 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ y) (M.op (σ x) X0)) := by
              intro X0 X1
              first
              | (have i₁ := b20e35 X1
                 have i₂ := b20e99 (σ y) X0
                 grind)
              | (have i₁ := b20e35 X1
                 have i₂ := b20e99 X0 (σ y)
                 grind)
              | exact superpose b20e99 b20e35
              | exact resolve b20e35 b20e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35 b20e99
            have b20e941 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) (M.op (σ x) X0)) := by
              intro X0
              first
              | (have i₁ := b20e154 x
                 have i₂ := b20e186 X0 x
                 grind)
              | exact superpose b20e186 b20e154
              | exact resolve b20e154 b20e186
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e154
            have b20e1166 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X0 (M.op X1 X0)) (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have j0 := b20e49 X0 X1 (M.op X0 (M.op X1 X0))
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e49
            have b20e1196 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              intro X0
              first
              | (have i₁ := b20e81 (σ x) (σ y) x
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e81
              | (have j0 := b20e81 (σ x) (σ y) x
                 grind)
              | exact resolve b20e81 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1256 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1
              grind
            have b20e1372 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1
              first
              | (have j0 := b20e81 X0 X0 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1376 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
              intro X0 X1
              first
              | (have j0 := b20e1372 X0 X1
                 have j1 := b20e17 X0 X0
                 grind)
              | (have r₁ := b20e1372 X0 X1
                 have r₂ := b20e17 X0 X0
                 grind)
              | exact resolve b20e1372 b20e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1372
            have b20e1392 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
              intro X0 X1
              first
              | (have j0 := b20e1256 X0 X1
                 have j1 := b20e17 X0 X0
                 grind)
              | (have r₁ := b20e1256 X0 X1
                 have r₂ := b20e17 X0 (M.op X0 X1)
                 grind)
              | (have r₁ := b20e1256 X0 X1
                 have r₂ := b20e17 X0 X0
                 grind)
              | exact resolve b20e1256 b20e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1256
            have b20e1400 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ (k y x)) := by
              intro X0
              first
              | (have i₁ := b20e1196 X0
                 have i₂ := b20e20 y x
                 grind)
              | exact superpose b20e20 b20e1196
              | (have j0 := b20e1196 X0
                 grind)
              | exact resolve b20e1196 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1196
            have b20e1404 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
              intro X0 X1
              first
              | (have i₁ := b20e1392 X0 X1
                 have i₂ := b20e14 X0 X1 X0
                 grind)
              | exact superpose b20e14 b20e1392
              | (have j0 := b20e1392 X0 X1
                 grind)
              | exact resolve b20e1392 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1392
            have b20e1409 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
              intro X0 X1
              first
              | (have j0 := b20e1404 X0 X1
                 have j1 := b20e1376 X0 X1
                 grind)
              | (have r₁ := b20e1404 X0 X1
                 have r₂ := b20e1376 X0 (M.op X1 X0)
                 grind)
              | exact resolve b20e1404 b20e1376
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1404
            have b20e1420 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e1376 X0 (M.op X1 X0)
                 have i₂ := b20e14 X0 X1 X2
                 grind)
              | exact superpose b20e14 b20e1376
              | (have j0 := b20e1376 X0 X1
                 grind)
              | exact resolve b20e1376 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1629 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b20e75 y y
                 have i₂ := b20e50
                 grind)
              | exact superpose b20e50 b20e75
              | exact resolve b20e75 b20e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e75
            have b20e1753 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k y y)) := by grind
            clear b20e1629
            have b20e1785 : (σ (k x y)) = (σ (k y y)) := by
              first
              | (have r₁ := b20e1753
                 have r₂ := b20e68
                 grind)
              | exact resolve b20e1753 b20e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e68 b20e1753
            have b20e1807 : (σ (k x y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b20e1785
                 have i₂ := b20e19 y y
                 grind)
              | exact superpose b20e19 b20e1785
              | (have j1 := b20e19 y y
                 grind)
              | exact resolve b20e1785 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1808 : (k y y) = (τ (σ (k x y))) := by
              first
              | (have i₁ := b20e15 (k y y)
                 have i₂ := b20e1785
                 grind)
              | exact superpose b20e1785 b20e15
              | exact resolve b20e15 b20e1785
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1785
            have b20e1818 : (σ (k x y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
            clear b20e1807
            have b20e1828 : (k x y) = (k y y) := by
              first
              | (have i₁ := b20e1808
                 have i₂ := b20e15 (k x y)
                 grind)
              | exact superpose b20e15 b20e1808
              | exact resolve b20e1808 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1808
            have b20e1886 : (M.op y y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b20e19 y y
                 have i₂ := b20e1828
                 grind)
              | exact superpose b20e1828 b20e19
              | (have j0 := b20e19 y y
                 grind)
              | exact resolve b20e19 b20e1828
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1887 : (M.op y y) = (k x y) ∨ y = (M.op y y) := by grind
            clear b20e1886
            have b20e2120 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              intro X0 X1
              first
              | (have i₁ := b20e100 X0 X1
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e100
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e100 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e2191 : ∀ X0 X1 X2 : G, (M.op (σ (k x y)) X0) = (M.op (M.op (σ (k x y)) X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e14 (σ (k x y)) X1 X2
                 have i₂ := b20e100 (M.op X1 (σ (k x y))) X0
                 grind)
              | (have i₁ := b20e14 (σ (k x y)) X1 X2
                 have i₂ := b20e100 X0 (M.op X1 (σ (k x y)))
                 grind)
              | exact superpose b20e100 b20e14
              | exact resolve b20e14 b20e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e100
            have b20e2237 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) ∨ x = (M.op y x) := by
              intro X0 X1
              first
              | (have j0 := b20e2120 X0 X1
                 grind)
              | (have r₁ := b20e2120 X0 X1
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e2120 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2120
            have b20e2251 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) := by
              intro X0 X1
              first
              | (have j0 := b20e2237 X0 X1
                 grind)
              | (have r₁ := b20e2237 X0 X1
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e2237 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2237
            have b20e2262 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b20e19 x y
                 have i₂ := b20e1887
                 grind)
              | exact superpose b20e1887 b20e19
              | (have j0 := b20e19 x y
                 grind)
              | exact resolve b20e19 b20e1887
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1887
            have b20e2263 : (M.op x y) = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
              first
              | (have r₁ := b20e2262
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e2262 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2262
            have b20e2273 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have r₁ := b20e2263
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e2263 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2263
            have b20e2481 : ∀ X0 : G, (M.op x y) = (M.op y X0) ∨ y = (M.op y X0) ∨ (M.op y y) = (k y y) ∨ y = (M.op y y) := by
              intro X0
              first
              | (have i₁ := b20e2273
                 have i₂ := b20e81 y y x
                 grind)
              | (have i₁ := b20e2273
                 have i₂ := b20e81 y x y
                 grind)
              | exact superpose b20e81 b20e2273
              | (have j1 := b20e81 y y x
                 grind)
              | exact resolve b20e2273 b20e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e81 b20e2273
            have b20e2520 : ∀ X0 : G, (M.op x y) = (M.op y X0) ∨ y = (M.op y X0) ∨ (M.op y y) = (k y y) := by
              intro X0
              first
              | (have j0 := b20e2481 X0
                 have j1 := b20e1376 y x
                 grind)
              | (have r₁ := b20e2481 x
                 have r₂ := b20e1376 y x
                 grind)
              | (have r₁ := b20e2481 X0
                 have r₂ := b20e1376 y y
                 grind)
              | exact resolve b20e2481 b20e1376
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2481
            have b20e2524 : ∀ X0 : G, (M.op x y) = (M.op y X0) ∨ (M.op y y) = (k y y) := by
              intro X0
              first
              | (have j0 := b20e2520 X0
                 have j1 := b20e1376 y x
                 grind)
              | (have r₁ := b20e2520 x
                 have r₂ := b20e1376 y x
                 grind)
              | exact resolve b20e2520 b20e1376
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2520
            have b20e2525 : ∀ X0 : G, (M.op y y) = (k x y) ∨ (M.op x y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b20e2524 X0
                 have i₂ := b20e1828
                 grind)
              | exact superpose b20e1828 b20e2524
              | (have j0 := b20e2524 X0
                 grind)
              | exact resolve b20e2524 b20e1828
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2524
            have b20e2871 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              intro X0
              first
              | (have i₁ := b20e67 X0
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e67
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e67 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e2898 : ∀ X0 X1 : G, (M.op (σ (k x y)) (σ y)) ≠ (M.op (M.op (σ (k x y)) X0) X1) ∨ (M.op (σ y) (σ y)) = (k (M.op (σ (k x y)) (σ y)) (σ y)) := by
              intro X0 X1
              first
              | (have i₁ := b20e46 (σ y) (σ (k x y)) X1
                 have i₂ := b20e67 X0
                 grind)
              | exact superpose b20e67 b20e46
              | (have j0 := b20e46 (σ y) (σ (k x y)) x
                 grind)
              | exact resolve b20e46 b20e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e2970 : (M.op (σ y) (σ y)) = (k (M.op (σ (k x y)) (σ y)) (σ y)) := by
              first
              | (have r₁ := b20e2898 x x
                 have r₂ := b20e2191 (σ y) x x
                 grind)
              | exact resolve b20e2898 b20e2191
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2191 b20e2898
            have b20e2981 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
              intro X0
              first
              | (have j0 := b20e2871 X0
                 grind)
              | (have r₁ := b20e2871 X0
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e2871 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2871
            have b20e2996 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ (k x y))) (σ y)) := by
              first
              | (have i₁ := b20e2970
                 have i₂ := b20e67 (σ y)
                 grind)
              | exact superpose b20e67 b20e2970
              | exact resolve b20e2970 b20e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e67 b20e2970
            have b20e3002 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ y) (σ (M.op x y))) := by
              intro X0
              first
              | (have j0 := b20e2981 X0
                 grind)
              | (have r₁ := b20e2981 X0
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e2981 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2981
            have b20e3009 : (σ (k x y)) = (k (M.op (σ y) (σ (k x y))) (σ y)) := by
              first
              | (have i₁ := b20e2996
                 have i₂ := b20e50
                 grind)
              | exact superpose b20e50 b20e2996
              | exact resolve b20e2996 b20e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2996
            have b20e3328 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
              intro X0 X1
              first
              | (have i₁ := b20e19 X0 (M.op X0 X1)
                 have i₂ := b20e1409 X0 X1
                 grind)
              | exact superpose b20e1409 b20e19
              | (have j0 := b20e19 X0 (M.op X0 X1)
                 have j1 := b20e1409 X0 X1
                 grind)
              | exact resolve b20e19 b20e1409
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1409
            have b20e3334 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
              intro X0 X1
              first
              | (have j0 := b20e3328 X0 X1
                 have j1 := b20e1376 X0 X1
                 grind)
              | (have r₁ := b20e3328 X0 X1
                 have r₂ := b20e1376 X0 (M.op X0 X1)
                 grind)
              | exact resolve b20e3328 b20e1376
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1376 b20e3328
            have b20e3363 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
              intro X0 X1
              first
              | (have j0 := b20e3334 X0 X1
                 have j1 := b20e1420 X0 X1 x
                 grind)
              | (have r₁ := b20e3334 x X1
                 have r₂ := b20e1420 x X1 x
                 grind)
              | exact resolve b20e3334 b20e1420
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1420 b20e3334
            have b20e3930 : ∀ X0 X1 X2 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (σ (M.op x y)) X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e14 (σ (M.op x y)) X1 X2
                 have i₂ := b20e2251 (M.op X1 (σ (M.op x y))) X0
                 grind)
              | (have i₁ := b20e14 (σ (M.op x y)) X1 X2
                 have i₂ := b20e2251 X0 (M.op X1 (σ (M.op x y)))
                 grind)
              | exact superpose b20e2251 b20e14
              | exact resolve b20e14 b20e2251
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2251
            have b20e14531 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ x) X0) (M.op (σ y) (σ x))) := by
              intro X0
              first
              | (have i₁ := b20e1166 (σ y) (σ x)
                 have i₂ := b20e186 (σ y) x
                 grind)
              | exact superpose b20e186 b20e1166
              | exact resolve b20e1166 b20e186
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e186 b20e1166
            have b20e14693 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ x) X0) (σ x)) := by
              intro X0
              first
              | (have i₁ := b20e14531 X0
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e14531
              | exact resolve b20e14531 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e14531
            have b20e14773 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k (τ (M.op (σ x) X0)) x) := by
              intro X0
              first
              | (have i₁ := b20e44 (M.op (σ x) X0) x
                 have i₂ := b20e14693 X0
                 grind)
              | exact superpose b20e14693 b20e44
              | exact resolve b20e44 b20e14693
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e44 b20e14693
            have b20e17478 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) X0) X1) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (M.op (σ (M.op x y)) (σ y)) (σ y)) := by
              intro X0 X1
              first
              | (have i₁ := b20e46 (σ y) (σ (M.op x y)) X1
                 have i₂ := b20e3002 X0
                 grind)
              | exact superpose b20e3002 b20e46
              | (have j0 := b20e46 (σ y) (σ (M.op x y)) x
                 grind)
              | exact resolve b20e46 b20e3002
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e46
            have b20e17534 : (M.op (σ y) (σ y)) = (k (M.op (σ (M.op x y)) (σ y)) (σ y)) := by
              first
              | (have r₁ := b20e17478 x x
                 have r₂ := b20e3930 (σ y) x x
                 grind)
              | exact resolve b20e17478 b20e3930
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e3930 b20e17478
            have b20e17595 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ (M.op x y))) (σ y)) := by
              first
              | (have i₁ := b20e17534
                 have i₂ := b20e3002 (σ y)
                 grind)
              | exact superpose b20e3002 b20e17534
              | exact resolve b20e17534 b20e3002
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e3002 b20e17534
            have b20e17625 : (σ (k x y)) = (k (M.op (σ y) (σ (M.op x y))) (σ y)) := by
              first
              | (have i₁ := b20e17595
                 have i₂ := b20e50
                 grind)
              | exact superpose b20e50 b20e17595
              | exact resolve b20e17595 b20e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e17595
            have b20e19563 : ∀ X0 : G, (M.op y y) = (k x y) ∨ (M.op y y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b20e1828
                 have i₂ := b20e3363 y X0
                 grind)
              | exact superpose b20e3363 b20e1828
              | (have j1 := b20e3363 y X0
                 grind)
              | exact resolve b20e1828 b20e3363
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1828 b20e3363
            have b20e26255 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ (M.op y y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b20e19 x y
                 have i₂ := b20e19563 X0
                 grind)
              | exact superpose b20e19563 b20e19
              | (have j0 := b20e19 x y
                 have j1 := b20e19563 X0
                 grind)
              | exact resolve b20e19 b20e19563
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e19563
            have b20e26518 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ x = (M.op y x) ∨ (M.op y y) = (M.op y X0) := by
              intro X0
              first
              | (have j0 := b20e26255 X0
                 grind)
              | (have r₁ := b20e26255 X0
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e26255 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e26255
            have b20e26570 : ∀ X0 : G, (M.op y y) = (M.op y X0) ∨ (M.op x y) = (M.op y y) := by
              intro X0
              first
              | (have j0 := b20e26518 X0
                 grind)
              | (have r₁ := b20e26518 X0
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e26518 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e26518
            have b20e31432 : ∀ X0 : G, x ≠ (M.op y X0) ∨ (M.op x y) = (M.op y y) := by
              intro X0
              first
              | (have i₁ := b20e26
                 have i₂ := b20e26570 X0
                 grind)
              | (have i₁ := b20e26
                 have i₂ := b20e26570 y
                 grind)
              | exact superpose b20e26570 b20e26
              | exact resolve b20e26 b20e26570
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e31609 : ∀ X0 : G, (M.op x y) ≠ (M.op y X0) ∨ (M.op x y) = (M.op y y) := by
              intro X0
              grind
            clear b20e26570
            have b20e41208 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b20e19 x y
                 have i₂ := b20e2525 X0
                 grind)
              | exact superpose b20e2525 b20e19
              | (have j0 := b20e19 x y
                 have j1 := b20e2525 y
                 grind)
              | exact resolve b20e19 b20e2525
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e2525
            have b20e41429 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have j0 := b20e41208 y
                 grind)
              | (have r₁ := b20e41208 x
                 have r₂ := b20e31609 y
                 grind)
              | (have r₁ := b20e41208 x
                 have r₂ := b20e31609 x
                 grind)
              | exact resolve b20e41208 b20e31609
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31609 b20e41208
            have b20e41473 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) := by
              first
              | (have r₁ := b20e41429
                 have r₂ := b20e31432 x
                 grind)
              | exact resolve b20e41429 b20e31432
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31432 b20e41429
            have b20e41485 : (M.op x y) = (M.op y y) := by
              first
              | (have r₁ := b20e41473
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e41473 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e41473
            have b20e42593 : x ≠ (M.op x y) := by
              first
              | (have i₁ := b20e26
                 have i₂ := b20e41485
                 grind)
              | exact superpose b20e41485 b20e26
              | exact resolve b20e26 b20e41485
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e109357 : (σ (M.op y y)) = (k (M.op (σ y) (σ (M.op y y))) (σ y)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b20e3009
                 have i₂ := b20e1818
                 grind)
              | exact superpose b20e1818 b20e3009
              | exact resolve b20e3009 b20e1818
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1818 b20e3009
            have b20e109393 : (σ (M.op x y)) = (k (M.op (σ y) (σ (M.op x y))) (σ y)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b20e109357
                 have i₂ := b20e41485
                 grind)
              | exact superpose b20e41485 b20e109357
              | exact resolve b20e109357 b20e41485
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e109357
            have b20e109405 : (σ (M.op x y)) = (σ (k x y)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b20e109393
                 have i₂ := b20e17625
                 grind)
              | exact superpose b20e17625 b20e109393
              | exact resolve b20e109393 b20e17625
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e17625 b20e109393
            have b20e109416 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ (k x y)) := by
              first
              | (have i₁ := b20e109405
                 have i₂ := b20e41485
                 grind)
              | exact superpose b20e41485 b20e109405
              | exact resolve b20e109405 b20e41485
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e41485 b20e109405
            have b20e109419 : (σ (M.op x y)) = (σ (k x y)) := by
              first
              | (have r₁ := b20e109416
                 have r₂ := b20e25
                 grind)
              | exact resolve b20e109416 b20e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e109416
            have b20e116201 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ (k y x)) := by
              intro X0
              first
              | (have i₁ := b20e941 (σ y)
                 have i₂ := b20e1400 X0
                 grind)
              | exact superpose b20e1400 b20e941
              | (have j1 := b20e1400 X0
                 grind)
              | exact resolve b20e941 b20e1400
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e941 b20e1400
            have b20e116744 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ (k y x)) := by
              intro X0
              first
              | (have i₁ := b20e116201 X0
                 have i₂ := b20e50
                 grind)
              | exact superpose b20e50 b20e116201
              | (have j0 := b20e116201 X0
                 grind)
              | exact resolve b20e116201 b20e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e50 b20e116201
            have b20e116808 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ (k y x)) := by
              intro X0
              first
              | (have j0 := b20e116744 X0
                 grind)
              | (have r₁ := b20e116744 X0
                 have r₂ := b20e109419
                 grind)
              | exact resolve b20e116744 b20e109419
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e109419 b20e116744
            have b20e123998 : ∀ X0 : G, (k y x) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b20e15 (k y x)
                 have i₂ := b20e116808 X0
                 grind)
              | exact superpose b20e116808 b20e15
              | (have j1 := b20e116808 X0
                 grind)
              | exact resolve b20e15 b20e116808
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e116808
            have b20e124041 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (k y x) := by
              intro X0
              first
              | (have i₁ := b20e123998 X0
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e123998
              | (have j0 := b20e123998 X0
                 grind)
              | exact resolve b20e123998 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e123998
            have b20e126964 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k y x) := by
              first
              | (have i₁ := b20e14773 x
                 have i₂ := b20e124041 x
                 grind)
              | exact superpose b20e124041 b20e14773
              | exact resolve b20e14773 b20e124041
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e14773 b20e124041
            have b20e127315 : x = (k y x) ∨ x = (k x x) := by
              first
              | (have i₁ := b20e126964
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e126964
              | exact resolve b20e126964 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e126964
            have b20e127403 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (k x x) := by
              first
              | (have i₁ := b20e19 y x
                 have i₂ := b20e127315
                 grind)
              | exact superpose b20e127315 b20e19
              | (have j0 := b20e19 y x
                 grind)
              | exact resolve b20e19 b20e127315
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e127315
            have b20e127414 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (k x x) := by
              first
              | (have r₁ := b20e127403
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e127403 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e127403
            have b20e127426 : y = (M.op x y) ∨ x = (k x x) := by
              first
              | (have r₁ := b20e127414
                 have r₂ := b20e26
                 grind)
              | exact resolve b20e127414 b20e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e127414
            have b20e127433 : x = (k x x) := by
              first
              | (have r₁ := b20e127426
                 have r₂ := b20e25
                 grind)
              | exact resolve b20e127426 b20e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e127426
            have b20e129492 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b20e19 x x
                 have i₂ := b20e127433
                 grind)
              | exact superpose b20e127433 b20e19
              | (have j0 := b20e19 x x
                 grind)
              | exact resolve b20e19 b20e127433
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e127433
            have b20e129501 : x = (M.op x x) := by grind
            clear b20e129492
            have b20e132239 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
              intro X0 X1
              first
              | (have i₁ := b20e33 x x x x
                 have i₂ := b20e129501
                 grind)
              | exact superpose b20e129501 b20e33
              | exact resolve b20e33 b20e129501
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e33
            have b20e136376 : ∀ X0 : G, x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b20e129501
                 have i₂ := b20e132239 x X0
                 grind)
              | (have i₁ := b20e129501
                 have i₂ := b20e132239 X0 x
                 grind)
              | exact superpose b20e132239 b20e129501
              | exact resolve b20e129501 b20e132239
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e129501
            have b20e136386 : ∀ X0 : G, x ≠ (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b20e42593
                 have i₂ := b20e132239 y X0
                 grind)
              | (have i₁ := b20e42593
                 have i₂ := b20e132239 X0 y
                 grind)
              | exact superpose b20e132239 b20e42593
              | exact resolve b20e42593 b20e132239
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e42593 b20e132239
            have b20e136400 : False := by grind
            exact b20e136400
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : x ≠ (M.op y x) := by grind
            have b21e23 : y ≠ (M.op x x) := by grind
            have b21e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b21e25 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b21e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e68 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b21e69 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e68
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e68 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e68
            have b21e71 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e69
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e69
              | exact resolve b21e69 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e69
            have b21e84 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b21e71
                 have i₂ := b21e19 x y
                 grind)
              | exact superpose b21e19 b21e71
              | (have j1 := b21e19 x y
                 grind)
              | exact resolve b21e71 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e71
            have b21e93 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
              first
              | (have r₁ := b21e84
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e84 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e84
            have b21e94 : (σ (M.op x y)) = (σ x) := by
              first
              | (have r₁ := b21e93
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e93 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e93
            have b21e95 : (σ x) = (σ y) := by
              first
              | (have i₁ := b21e94
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e94
              | exact resolve b21e94 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e94
            have b21e111 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b21e24
                 have i₂ := b21e95
                 grind)
              | exact superpose b21e95 b21e24
              | exact resolve b21e24 b21e95
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e118 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b21e111
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e111
              | exact resolve b21e111 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e111
            have b21e120 : False := by grind
            exact b21e120
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : x ≠ (M.op y x) := by grind
              have b22e24 : y ≠ (M.op x x) := by grind
              have b22e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b22e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              have b22e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e45 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b22e15 y y x
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e15
                | exact resolve b22e15 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e50 : ∀ X0 : G, x ≠ (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b22e23
                   have i₂ := b22e45 X0
                   grind)
                | exact superpose b22e45 b22e23
                | exact resolve b22e23 b22e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e45
              have b22e68 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
              have b22e73 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e68
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e68 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e68
              have b22e76 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b22e73
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e73
                | exact resolve b22e73 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e73
              have b22e95 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e76
                   grind)
                | exact superpose b22e76 b22e16
                | exact resolve b22e16 b22e76
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e76
              have b22e96 : x = (k x y) := by
                first
                | (have i₁ := b22e95
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e95
                | exact resolve b22e95 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e95
              have b22e102 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e96
                   grind)
                | exact superpose b22e96 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e96
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e96
              have b22e103 : y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b22e102
                   have r₂ := b22e50 y
                   grind)
                | exact resolve b22e102 b22e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e50 b22e102
              have b22e105 : x = (M.op y x) := by
                first
                | (have r₁ := b22e103
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e103 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e103
              have b22e107 : False := by grind
              exact b22e107
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : x ≠ (M.op y x) := by grind
              have b23e24 : y ≠ (M.op x x) := by grind
              have b23e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b23e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              have b23e27 : y ≠ (M.op x y) := by grind
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
              have b23e78 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
              have b23e85 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e78
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e78 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e78
              have b23e88 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b23e85
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e85
                | exact resolve b23e85 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e85
              have b23e92 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e88
                   grind)
                | exact superpose b23e88 b23e16
                | exact resolve b23e16 b23e88
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e88
              have b23e93 : x = (k x y) := by
                first
                | (have i₁ := b23e92
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e92
                | exact resolve b23e92 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e92
              have b23e102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b23e21 X0 X1
                   have i₂ := b23e20 (σ X0) (σ X1)
                   grind)
                | exact superpose b23e20 b23e21
                | (have j1 := b23e20 (σ X0) (σ X1)
                   grind)
                | exact resolve b23e21 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e116 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e93
                   grind)
                | exact superpose b23e93 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e93
              have b23e117 : x = (M.op x y) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b23e116
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e116 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e116
              have b23e119 : x = (M.op x y) := by
                first
                | (have r₁ := b23e117
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e117 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e117
              have b23e159 : x ≠ y := by
                first
                | (have i₁ := b23e27
                   have i₂ := b23e119
                   grind)
                | exact superpose b23e119 b23e27
                | exact resolve b23e27 b23e119
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e160 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
                intro X0 X1
                first
                | (have i₁ := b23e39 x y x x
                   have i₂ := b23e119
                   grind)
                | exact superpose b23e119 b23e39
                | exact resolve b23e39 b23e119
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e39
              have b23e319 : ∀ X0 X1 : G, (M.op x X0) ≠ X1 ∨ (M.op x x) = (k X1 x) := by
                intro X0 X1
                first
                | (have i₁ := b23e18 X1 x
                   have i₂ := b23e160 X1 X0
                   grind)
                | (have i₁ := b23e18 X1 x
                   have i₂ := b23e160 X0 X1
                   grind)
                | exact superpose b23e160 b23e18
                | (have j0 := b23e18 X1 x
                   grind)
                | (have r₁ := b23e18 (M.op x X1) x
                   have r₂ := b23e160 (M.op x X1) X1
                   grind)
                | (have r₁ := b23e18 (M.op x X0) x
                   have r₂ := b23e160 X0 (M.op x X0)
                   grind)
                | exact resolve b23e18 b23e160
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e327 : ∀ X0 : G, x = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b23e119
                   have i₂ := b23e160 y X0
                   grind)
                | (have i₁ := b23e119
                   have i₂ := b23e160 X0 y
                   grind)
                | exact superpose b23e160 b23e119
                | exact resolve b23e119 b23e160
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e119 b23e160
              have b23e333 : ∀ X1 : G, x ≠ X1 ∨ (M.op x x) = (k X1 x) := by
                intro X1
                first
                | (have i₁ := b23e319 x X1
                   have i₂ := b23e327 x
                   grind)
                | exact superpose b23e327 b23e319
                | (have j0 := b23e319 x X1
                   grind)
                | (have r₁ := b23e319 x x
                   have r₂ := b23e327 x
                   grind)
                | exact resolve b23e319 b23e327
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e319
              have b23e346 : ∀ X1 : G, x ≠ X1 ∨ x = (k X1 x) := by
                intro X1
                first
                | (have i₁ := b23e333 X1
                   have i₂ := b23e327 x
                   grind)
                | exact superpose b23e327 b23e333
                | (have j0 := b23e333 X1
                   grind)
                | (have r₁ := b23e333 (M.op x x)
                   have r₂ := b23e327 x
                   grind)
                | exact resolve b23e333 b23e327
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e327 b23e333
              have b23e909 : x = (k x x) := by
                first
                | (have j0 := b23e346 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e346
              have b23e1411 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b23e26
                   have i₂ := b23e102 x x
                   grind)
                | exact superpose b23e102 b23e26
                | (have j1 := b23e102 x x
                   grind)
                | exact resolve b23e26 b23e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e102
              have b23e1500 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
              clear b23e1411
              have b23e1535 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b23e1500
                   have i₂ := b23e909
                   grind)
                | exact superpose b23e909 b23e1500
                | exact resolve b23e1500 b23e909
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e909 b23e1500
              have b23e1571 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b23e1535
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e1535
                | exact resolve b23e1535 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1535
              have b23e1572 : (σ x) = (σ y) := by grind
              clear b23e1571
              have b23e1587 : y = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 y
                   have i₂ := b23e1572
                   grind)
                | exact superpose b23e1572 b23e16
                | exact resolve b23e16 b23e1572
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1572
              have b23e1601 : x = y := by
                first
                | (have i₁ := b23e1587
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e1587
                | exact resolve b23e1587 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1587
              have b23e1607 : False := by grind
              exact b23e1607
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b24e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : x ≠ (M.op y x) := by grind
            have b24e23 : y ≠ (M.op x x) := by grind
            have b24e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b24e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b24e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e21
              | exact resolve b24e21 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e102 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
            have b24e1641 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b24e102 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e102
            have b24e1642 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b24e1641
                 have r₂ := b24e24
                 grind)
              | exact resolve b24e1641 b24e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1641
            have b24e1643 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b24e1642
                 have i₂ := b24e20 x y
                 grind)
              | exact superpose b24e20 b24e1642
              | exact resolve b24e1642 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1642
            have b24e1646 : (σ y) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b24e28
                 have i₂ := b24e1643
                 grind)
              | exact superpose b24e1643 b24e28
              | exact resolve b24e28 b24e1643
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e28 b24e1643
            have b24e1835 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b24e1646
                 have i₂ := b24e19 x y
                 grind)
              | exact superpose b24e19 b24e1646
              | (have j1 := b24e19 x y
                 grind)
              | exact resolve b24e1646 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1646
            have b24e1836 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y x) := by
              first
              | (have r₁ := b24e1835
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e1835 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1835
            have b24e1839 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have r₁ := b24e1836
                 have r₂ := b24e22
                 grind)
              | exact resolve b24e1836 b24e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1836
            have b24e1844 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b24e1839
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e1839
              | exact resolve b24e1839 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1839
            have b24e1845 : False := by grind
            exact b24e1845
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b25e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e23 : x ≠ (M.op y x) := by grind
              have b25e24 : y ≠ (M.op x x) := by grind
              have b25e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b25e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e82 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
              have b25e1217 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b25e82 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e82
              have b25e1218 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b25e1217
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e1217 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1217
              have b25e1219 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b25e1218
                   have i₂ := b25e21 x y
                   grind)
                | exact superpose b25e21 b25e1218
                | exact resolve b25e1218 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1218
              have b25e1675 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e1219
                   grind)
                | exact superpose b25e1219 b25e22
                | exact resolve b25e22 b25e1219
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1219
              have b25e2124 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b25e1675
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e1675
                | (have j1 := b25e20 x y
                   grind)
                | exact resolve b25e1675 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1675
              have b25e2125 : y = (M.op x x) ∨ x = (M.op y x) := by grind
              clear b25e2124
              have b25e2130 : x = (M.op y x) := by
                first
                | (have r₁ := b25e2125
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e2125 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2125
              have b25e2135 : False := by grind
              exact b25e2135
            · have b26e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : x ≠ (M.op y x) := by grind
              have b26e24 : y ≠ (M.op x x) := by grind
              have b26e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b26e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e97 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
              have b26e1848 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b26e97 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e97
              have b26e1849 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b26e1848
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e1848 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1848
              have b26e1850 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e1849
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e1849
                | exact resolve b26e1849 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1849
              have b26e1853 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e1850
                   grind)
                | exact superpose b26e1850 b26e22
                | exact resolve b26e22 b26e1850
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1850
              have b26e1995 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b26e1853
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e1853
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e1853 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1853
              have b26e1996 : y = (M.op x x) ∨ x = (M.op y x) := by grind
              clear b26e1995
              have b26e1999 : x = (M.op y x) := by
                first
                | (have r₁ := b26e1996
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e1996 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1996
              have b26e2002 : False := by grind
              exact b26e2002

/-- `Equation4437`: `x ◇ (y ◇ x) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pyx_pxy_Equation4437 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b0e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b0e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b0e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e18 (τ X0) X1
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e18
          | exact resolve b0e18 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e12 (M.op X0 X1) X2 X3
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
        have b0e50 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
          intro X0 X1 X3
          first
          | (have i₁ := b0e41 X0 X1 x X3
             have i₂ := b0e12 X0 X1 (M.op x (M.op X0 X1))
             grind)
          | exact superpose b0e12 b0e41
          | exact resolve b0e41 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41
        have b0e82 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e16 X0 X1
             have i₂ := b0e17 X2 X0
             grind)
          | exact superpose b0e17 b0e16
          | (have j0 := b0e16 X0 X1
             have j1 := b0e17 X1 X1
             grind)
          | (have r₁ := b0e16 X1 X1
             have r₂ := b0e17 X0 X1
             grind)
          | (have r₁ := b0e16 X0 X1
             have r₂ := b0e17 X0 X1
             grind)
          | exact resolve b0e16 b0e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e99 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b0e82 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e82
        have b0e114 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b0e29 X0 x
             have i₂ := b0e27 (τ X0)
             grind)
          | exact superpose b0e27 b0e29
          | exact resolve b0e29 b0e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e27 b0e29
        have b0e120 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b0e114 X0
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e114
          | exact resolve b0e114 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e114
        have b0e2319 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b0e99 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e99
        have b0e2320 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b0e2319 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2319
        have b0e2321 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b0e2320 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2320
        have b0e3886 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e120 (σ x)
             have i₂ := b0e2321 (σ x)
             grind)
          | exact superpose b0e2321 b0e120
          | (have j1 := b0e2321 (σ x)
             grind)
          | exact resolve b0e120 b0e2321
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e120 b0e2321
        have b0e3905 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b0e3886
        have b0e3977 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) X0) := by
          intro X0
          first
          | (have i₁ := b0e50 (σ x) (σ x) x
             have i₂ := b0e3905
             grind)
          | exact superpose b0e3905 b0e50
          | exact resolve b0e50 b0e3905
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e50
        have b0e3989 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e3977 X0
             have i₂ := b0e3905
             grind)
          | exact superpose b0e3905 b0e3977
          | exact resolve b0e3977 b0e3905
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e3905 b0e3977
        have b0e4350 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e3989 (σ y)
             grind)
          | exact superpose b0e3989 b0e19
          | exact resolve b0e19 b0e3989
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e3989
        have b0e4414 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b0e4350
             have i₂ := b0e48 y
             grind)
          | exact superpose b0e48 b0e4350
          | exact resolve b0e4350 b0e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48 b0e4350
        have b0e4415 : False := by grind
        exact b0e4415
      · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b1e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b1e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b1e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
          have b1e23 : x ≠ (M.op x x) := by grind
          have b1e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X1 (τ X0)
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e19
            | exact resolve b1e19 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e45 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X0 X1 X3
               have i₂ := b1e13 X0 X1 X2
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e50 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b1e13 y y x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e53 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b1e50 X0
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e50
            | exact resolve b1e50 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e50
          have b1e65 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e17 (σ y) X0
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e17
            | (have j0 := b1e17 (σ y) X0
               grind)
            | (have r₁ := b1e17 (σ y) x
               have r₂ := b1e22
               grind)
            | exact resolve b1e17 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e67 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b1e17 y X0
               have i₂ := b1e53 y
               grind)
            | exact superpose b1e53 b1e17
            | (have j0 := b1e17 y X0
               grind)
            | (have r₁ := b1e17 y x
               have r₂ := b1e53 y
               grind)
            | exact resolve b1e17 b1e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e53
          have b1e68 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have j0 := b1e67 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e67
          have b1e70 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have j0 := b1e65 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e65
          have b1e99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X0 X1
               have i₂ := b1e18 (σ X0) (σ X1)
               grind)
            | exact superpose b1e18 b1e19
            | (have j1 := b1e18 (σ X1) (σ X1)
               grind)
            | exact resolve b1e19 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e117 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e14 (k X0 (τ X1))
               have i₂ := b1e30 X1 X0
               grind)
            | exact superpose b1e30 b1e14
            | exact resolve b1e14 b1e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e382 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e16 X1 X0
               have i₂ := b1e70 X0
               grind)
            | exact superpose b1e70 b1e16
            | (have j0 := b1e16 X1 X0
               have j1 := b1e70 X0
               grind)
            | (have r₁ := b1e16 X0 X0
               have r₂ := b1e70 X0
               grind)
            | exact resolve b1e16 b1e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e70
          have b1e401 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0 X1
            first
            | (have j0 := b1e382 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e382
          have b1e2829 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b1e99 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e99
          have b1e2830 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b1e2829 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e2829
          have b1e3125 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e45 X0 X0 X2 x
               have i₂ := b1e68 X0
               grind)
            | exact superpose b1e68 b1e45
            | (have j1 := b1e68 X0
               grind)
            | exact resolve b1e45 b1e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e45
          have b1e4230 : ∀ X0 X1 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (k X1 (σ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e19 y X0
               have i₂ := b1e401 (σ X0) X1
               grind)
            | exact superpose b1e401 b1e19
            | (have j1 := b1e401 (σ X0) X1
               grind)
            | exact resolve b1e19 b1e401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e401
          have b1e11561 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b1e2830 (τ X0)
               have i₂ := b1e30 X0 (τ X0)
               grind)
            | exact superpose b1e30 b1e2830
            | (have j0 := b1e2830 (τ X0)
               grind)
            | exact resolve b1e2830 b1e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e30 b1e2830
          have b1e11601 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b1e11561 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e11561
            | (have j0 := b1e11561 X0
               grind)
            | exact resolve b1e11561 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e11561
          have b1e11624 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e11601 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e11601
            | (have j0 := b1e11601 X0
               grind)
            | exact resolve b1e11601 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e11601
          have b1e427436 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x y) = (k y x) := by
            intro X0
            first
            | (have i₁ := b1e23
               have i₂ := b1e3125 x x X0
               grind)
            | (have i₁ := b1e23
               have i₂ := b1e3125 x X0 x
               grind)
            | exact superpose b1e3125 b1e23
            | (have j1 := b1e3125 x x x
               grind)
            | exact resolve b1e23 b1e3125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e427446 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 y) = (k y X0) ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e68 X0
               have i₂ := b1e3125 X0 X0 X1
               grind)
            | (have i₁ := b1e68 X0
               have i₂ := b1e3125 X0 X1 X0
               grind)
            | exact superpose b1e3125 b1e68
            | (have j0 := b1e68 X0
               have j1 := b1e3125 X0 X1 x
               grind)
            | exact resolve b1e68 b1e3125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e68 b1e3125
          have b1e428018 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1
            first
            | (have j0 := b1e427446 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e427446
          have b1e428036 : (M.op x y) = (k y x) := by
            first
            | (have j1 := b1e428018 x x
               grind)
            | (have r₁ := b1e427436 x
               have r₂ := b1e428018 x x
               grind)
            | exact resolve b1e427436 b1e428018
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e427436 b1e428018
          have b1e982424 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b1e20
               have i₂ := b1e4230 x X0
               grind)
            | exact superpose b1e4230 b1e20
            | (have j1 := b1e4230 x X0
               grind)
            | exact resolve b1e20 b1e4230
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e4230
          have b1e982437 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b1e982424 X0
               have i₂ := b1e428036
               grind)
            | exact superpose b1e428036 b1e982424
            | (have j0 := b1e982424 X0
               grind)
            | exact resolve b1e982424 b1e428036
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e428036 b1e982424
          have b1e982438 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have j0 := b1e982437 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e982437
          have b1e982476 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) := by
            intro X0
            first
            | (have i₁ := b1e117 X0 (σ x)
               have i₂ := b1e982438 (σ X0)
               grind)
            | exact superpose b1e982438 b1e117
            | exact resolve b1e117 b1e982438
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e117 b1e982438
          have b1e982503 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b1e982476 X0
               have i₂ := b1e14 x
               grind)
            | exact superpose b1e14 b1e982476
            | exact resolve b1e982476 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e982476
          have b1e982515 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b1e982503 X0
               have i₂ := b1e14 X0
               grind)
            | exact superpose b1e14 b1e982503
            | exact resolve b1e982503 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e982503
          have b1e982564 : x ≠ x ∨ x = (M.op x x) := by
            first
            | (have i₁ := b1e11624 x
               have i₂ := b1e982515 x
               grind)
            | exact superpose b1e982515 b1e11624
            | (have j0 := b1e11624 x
               grind)
            | (have r₁ := b1e11624 x
               have r₂ := b1e982515 x
               grind)
            | exact resolve b1e11624 b1e982515
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e11624 b1e982515
          have b1e982606 : x = (M.op x x) := by grind
          clear b1e982564
          have b1e982624 : False := by grind
          exact b1e982624
        · have b2e21 : y = (M.op y y) := by grind
          have b2e24 : y ≠ (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e25 : False := by grind
          exact b2e25
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e23 : (σ x) = (M.op (σ x) (σ x)) := by grind
          have b3e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e42 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b3e13 (σ x) (σ x) x
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e13
            | exact resolve b3e13 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e43 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
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
          have b3e48 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b3e43 X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e43
            | exact resolve b3e43 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e43
          have b3e49 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b3e42 X0
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e42
            | exact resolve b3e42 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e42
          have b3e107 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e49 (σ y)
               grind)
            | exact superpose b3e49 b3e20
            | exact resolve b3e20 b3e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e49
          have b3e117 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e107
               have i₂ := b3e48 y
               grind)
            | exact superpose b3e48 b3e107
            | exact resolve b3e107 b3e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e48 b3e107
          have b3e118 : False := by grind
          exact b3e118
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b4e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b4e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b4e17 X0 y
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e17
              | (have j0 := b4e17 X0 y
                 grind)
              | (have r₁ := b4e17 X0 y
                 have r₂ := b4e26
                 grind)
              | exact resolve b4e17 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e30 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b4e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e27
            have b4e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b4e20 (τ X0) X1
                 have i₂ := b4e16 X0
                 grind)
              | exact superpose b4e16 b4e20
              | exact resolve b4e20 b4e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e93 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b4e23
                 have i₂ := b4e19 (σ y) X0
                 grind)
              | exact superpose b4e19 b4e23
              | (have j1 := b4e19 X0 X0
                 grind)
              | (have r₁ := b4e23
                 have r₂ := b4e19 X0 (σ y)
                 grind)
              | (have r₁ := b4e23
                 have r₂ := b4e19 (σ y) x
                 grind)
              | exact resolve b4e23 b4e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e97 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have j0 := b4e93 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e93
            have b4e112 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b4e31 X0 y
                 have i₂ := b4e30 (τ X0)
                 grind)
              | exact superpose b4e30 b4e31
              | exact resolve b4e31 b4e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e30 b4e31
            have b4e123 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b4e112 X0
                 have i₂ := b4e16 X0
                 grind)
              | exact superpose b4e16 b4e112
              | exact resolve b4e112 b4e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e112
            have b4e417 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b4e123 (σ y)
                 have i₂ := b4e97 (σ y)
                 grind)
              | exact superpose b4e97 b4e123
              | (have j1 := b4e97 (σ y)
                 grind)
              | exact resolve b4e123 b4e97
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e97 b4e123
            have b4e422 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b4e417
            have b4e428 : False := by grind
            exact b4e428
          · have b5e22 : y = (M.op y y) := by grind
            have b5e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e27 : False := by grind
            exact b5e27
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b6e16 X0 x
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e16
            | (have j0 := b6e16 X0 x
               grind)
            | (have r₁ := b6e16 X0 x
               have r₂ := b6e24
               grind)
            | exact resolve b6e16 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e27 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b6e26 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26
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
          have b6e86 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b6e23
               have i₂ := b6e18 (σ x) X0
               grind)
            | exact superpose b6e18 b6e23
            | (have j1 := b6e18 X0 X0
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 X0 (σ x)
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 (σ x) x
               grind)
            | exact resolve b6e23 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e90 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b6e86 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e86
          have b6e116 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e29 X0 x
               have i₂ := b6e27 (τ X0)
               grind)
            | exact superpose b6e27 b6e29
            | exact resolve b6e29 b6e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e27 b6e29
          have b6e123 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e116 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e116
            | exact resolve b6e116 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e116
          have b6e477 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e123 (σ x)
               have i₂ := b6e90 (σ x)
               grind)
            | exact superpose b6e90 b6e123
            | (have j1 := b6e90 (σ x)
               grind)
            | exact resolve b6e123 b6e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e90 b6e123
          have b6e481 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b6e477
          have b6e485 : False := by grind
          exact b6e485
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b7e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b7e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e27 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b7e17 X0 y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e17
              | (have j0 := b7e17 X0 y
                 grind)
              | (have r₁ := b7e17 X0 y
                 have r₂ := b7e26
                 grind)
              | exact resolve b7e17 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e28 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b7e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e27
            have b7e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 (τ X0) X1
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e20
              | exact resolve b7e20 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e32 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b7e29 X0 y
                 have i₂ := b7e28 (τ X0)
                 grind)
              | exact superpose b7e28 b7e29
              | exact resolve b7e29 b7e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e28 b7e29
            have b7e36 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b7e32 X0
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e32
              | exact resolve b7e32 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e32
            have b7e82 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b7e23
                 have i₂ := b7e19 (σ y) X0
                 grind)
              | exact superpose b7e19 b7e23
              | (have j1 := b7e19 X0 X0
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e19 X0 (σ y)
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e19 (σ y) x
                 grind)
              | exact resolve b7e23 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e89 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have j0 := b7e82 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e82
            have b7e401 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b7e36 (σ y)
                 have i₂ := b7e89 (σ y)
                 grind)
              | exact superpose b7e89 b7e36
              | (have j1 := b7e89 (σ y)
                 grind)
              | exact resolve b7e36 b7e89
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e36 b7e89
            have b7e404 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b7e401
            have b7e408 : False := by grind
            exact b7e408
          · have b8e22 : y = (M.op y y) := by grind
            have b8e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e27 : False := by grind
            exact b8e27
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b9e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : y ≠ (M.op y y) := by grind
          have b9e23 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e26 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
          have b9e27 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b9e26 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26
          have b9e32 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
            intro X0
            first
            | (have i₁ := b9e19 X0 y
               have i₂ := b9e27 (σ X0)
               grind)
            | exact superpose b9e27 b9e19
            | exact resolve b9e19 b9e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e27
          have b9e35 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b9e14 (k X0 y)
               have i₂ := b9e32 X0
               grind)
            | exact superpose b9e32 b9e14
            | exact resolve b9e14 b9e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e32
          have b9e36 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b9e35 X0
               have i₂ := b9e14 X0
               grind)
            | exact superpose b9e14 b9e35
            | exact resolve b9e35 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e35
          have b9e75 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b9e17 X0 X1
               have i₂ := b9e18 X2 X0
               grind)
            | exact superpose b9e18 b9e17
            | (have j0 := b9e17 X0 X1
               have j1 := b9e18 X1 X1
               grind)
            | (have r₁ := b9e17 X1 X1
               have r₂ := b9e18 X0 X1
               grind)
            | (have r₁ := b9e17 X0 X1
               have r₂ := b9e18 X0 X1
               grind)
            | exact resolve b9e17 b9e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e93 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b9e75 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e75
          have b9e2071 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b9e93 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e93
          have b9e2072 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b9e2071 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e2071
          have b9e2073 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b9e2072 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e2072
          have b9e3595 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b9e36 y
               have i₂ := b9e2073 y
               grind)
            | exact superpose b9e2073 b9e36
            | (have j1 := b9e2073 y
               grind)
            | exact resolve b9e36 b9e2073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e36 b9e2073
          have b9e3600 : y = (M.op y y) := by grind
          clear b9e3595
          have b9e3652 : False := by grind
          exact b9e3652
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b10e23 : x = (M.op x x) := by grind
            have b10e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e27 : False := by grind
            exact b10e27
          · have b11e23 : x = (M.op x x) := by grind
            have b11e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : False := by grind
            exact b11e27
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e25 : (σ x) = (M.op (σ x) (σ x)) := by grind
            have b12e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e43 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b12e14 (σ x) (σ x) x
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e14
              | exact resolve b12e14 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e44 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b12e14 x x x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e47 : ∀ X0 : G, x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b12e44 X0
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e44
              | exact resolve b12e44 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e44
            have b12e48 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b12e43 X0
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e43
              | exact resolve b12e43 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e43
            have b12e66 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e48 (σ y)
                 grind)
              | exact superpose b12e48 b12e21
              | exact resolve b12e21 b12e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e48
            have b12e76 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b12e66
                 have i₂ := b12e47 y
                 grind)
              | exact superpose b12e47 b12e66
              | exact resolve b12e66 b12e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e47 b12e66
            have b12e77 : False := by grind
            exact b12e77
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b13e24 : x = (M.op x x) := by grind
              have b13e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : False := by grind
              exact b13e29
            · have b14e24 : x = (M.op x x) := by grind
              have b14e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : False := by grind
              exact b14e29
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e25 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e27 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
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
            have b15e28 : ∀ X0 : G, (k X0 x) = X0 := by
              intro X0
              first
              | (have j0 := b15e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e27
            have b15e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 (τ X0) X1
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e20
              | exact resolve b15e20 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e32 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b15e29 X0 x
                 have i₂ := b15e28 (τ X0)
                 grind)
              | exact superpose b15e28 b15e29
              | exact resolve b15e29 b15e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28 b15e29
            have b15e36 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b15e32 X0
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e32
              | exact resolve b15e32 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e32
            have b15e83 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b15e25
                 have i₂ := b15e19 (σ x) X0
                 grind)
              | exact superpose b15e19 b15e25
              | (have j1 := b15e19 X0 X0
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 X0 (σ x)
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 (σ x) x
                 grind)
              | exact resolve b15e25 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e88 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
              intro X0
              first
              | (have j0 := b15e83 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e83
            have b15e367 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e36 (σ x)
                 have i₂ := b15e88 (σ x)
                 grind)
              | exact superpose b15e88 b15e36
              | (have j1 := b15e88 (σ x)
                 grind)
              | exact resolve b15e36 b15e88
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e36 b15e88
            have b15e370 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b15e367
            have b15e374 : False := by grind
            exact b15e374
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b16e24 : x = (M.op x x) := by grind
              have b16e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e29 : False := by grind
              exact b16e29
            · have b17e24 : x = (M.op x x) := by grind
              have b17e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e29 : False := by grind
              exact b17e29
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e22 : x ≠ (M.op x x) := by grind
          have b18e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e25 : False := by grind
          exact b18e25
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b19e22 : y ≠ (M.op y y) := by grind
            have b19e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e27 : False := by grind
            exact b19e27
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            have b20e26 : y ≠ (M.op y y) := by grind
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
              | (have i₁ := b20e28 (σ X0)
                 have i₂ := b20e20 X0 y
                 grind)
              | exact superpose b20e20 b20e28
              | exact resolve b20e28 b20e20
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
            have b20e96 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b20e36 X0
                 have i₂ := b20e19 X0 y
                 grind)
              | exact superpose b20e19 b20e36
              | (have j1 := b20e19 y y
                 grind)
              | exact resolve b20e36 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e36
            have b20e104 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b20e96 X0
                 grind)
              | (have r₁ := b20e96 y
                 have r₂ := b20e26
                 grind)
              | (have r₁ := b20e96 X0
                 have r₂ := b20e26
                 grind)
              | exact resolve b20e96 b20e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e96
            have b20e2782 : y ≠ y ∨ y = (M.op y y) := by
              first
              | (have j0 := b20e104 y
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e104
            have b20e2783 : y = (M.op y y) := by grind
            clear b20e2782
            have b20e2797 : False := by grind
            exact b20e2797
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e23 : x ≠ (M.op x x) := by grind
            have b21e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e27 : False := by grind
            exact b21e27
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b22e23 : y ≠ (M.op y y) := by grind
              have b22e28 : y = (M.op y y) := by grind
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
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b23e26 : (σ x) = (M.op (σ x) (σ x)) := by grind
              have b23e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e18 X0 (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e18
                | (have j0 := b23e18 X0 (σ x)
                   grind)
                | (have r₁ := b23e18 X0 (σ x)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e18 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e30 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have j0 := b23e29 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e29
              have b23e34 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
                intro X0
                first
                | (have i₁ := b23e21 X0 x
                   have i₂ := b23e30 (σ X0)
                   grind)
                | exact superpose b23e30 b23e21
                | exact resolve b23e21 b23e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e30
              have b23e37 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
                intro X0
                first
                | (have i₁ := b23e16 (k X0 x)
                   have i₂ := b23e34 X0
                   grind)
                | exact superpose b23e34 b23e16
                | exact resolve b23e16 b23e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e34
              have b23e38 : ∀ X0 : G, (k X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e37 X0
                   have i₂ := b23e16 X0
                   grind)
                | exact superpose b23e16 b23e37
                | exact resolve b23e37 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e37
              have b23e49 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X0 X1 (M.op X2 (M.op X0 X1))
                   have i₂ := b23e15 (M.op X0 X1) X2 X3
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e86 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b23e25
                   have i₂ := b23e20 (σ y) X0
                   grind)
                | exact superpose b23e20 b23e25
                | (have j1 := b23e20 X0 X0
                   grind)
                | (have r₁ := b23e25
                   have r₂ := b23e20 X0 (σ y)
                   grind)
                | (have r₁ := b23e25
                   have r₂ := b23e20 (σ y) x
                   grind)
                | exact resolve b23e25 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e91 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
                intro X0
                first
                | (have j0 := b23e86 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e86
              have b23e232 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X0 X1) X2) ∨ (k X3 (M.op (M.op X0 X1) X2)) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e18 X3 (M.op (M.op X0 X1) X2)
                   have i₂ := b23e49 X0 X1 X2 (M.op (M.op X0 X1) X2)
                   grind)
                | exact superpose b23e49 b23e18
                | (have j0 := b23e18 X3 (M.op (M.op X0 X1) X2)
                   grind)
                | exact resolve b23e18 b23e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e49
              have b23e238 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op X0 X1) X2)) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have j0 := b23e232 X0 X1 X2 X3
                   grind)
                | (have r₁ := b23e232 X0 X1 X2 X3
                   have r₂ := b23e15 X0 X1 X2
                   grind)
                | exact resolve b23e232 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e232
              have b23e430 : (σ y) = (M.op (σ y) x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b23e38 (σ y)
                   have i₂ := b23e91 x
                   grind)
                | exact superpose b23e91 b23e38
                | (have j1 := b23e91 x
                   grind)
                | exact resolve b23e38 b23e91
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e38
              have b23e435 : (σ y) = (M.op (σ y) x) := by
                first
                | (have r₁ := b23e430
                   have r₂ := b23e27
                   grind)
                | exact resolve b23e430 b23e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e430
              have b23e441 : ∀ X0 X1 : G, (k X0 (M.op (σ y) X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b23e238 (σ y) x X1 X0
                   have i₂ := b23e435
                   grind)
                | exact superpose b23e435 b23e238
                | exact resolve b23e238 b23e435
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e238
              have b23e669 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e441 X0 x
                   have i₂ := b23e435
                   grind)
                | exact superpose b23e435 b23e441
                | exact resolve b23e441 b23e435
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e435 b23e441
              have b23e924 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b23e91 (σ y)
                   have i₂ := b23e669 (σ y)
                   grind)
                | exact superpose b23e669 b23e91
                | (have j0 := b23e91 (σ y)
                   grind)
                | exact resolve b23e91 b23e669
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e91 b23e669
              have b23e927 : (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b23e924
              have b23e931 : False := by grind
              exact b23e931
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e23 : x ≠ (M.op x x) := by grind
            have b24e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e27 : False := by grind
            exact b24e27
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b25e23 : y ≠ (M.op y y) := by grind
              have b25e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e29 : False := by grind
              exact b25e29
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
              have b26e27 : x ≠ (M.op x x) := by grind
              have b26e28 : y ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X0 X1 X3
                   have i₂ := b26e15 X0 X1 X2
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e70 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b26e26
                   have i₂ := b26e20 (σ x) X0
                   grind)
                | exact superpose b26e20 b26e26
                | (have j1 := b26e20 X0 X0
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 X0 (σ x)
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ x) x
                   grind)
                | exact resolve b26e26 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e74 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
                intro X0
                first
                | (have j0 := b26e70 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e70
              have b26e301 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e33 X0 X0 X2 x
                   have i₂ := b26e74 X0
                   grind)
                | exact superpose b26e74 b26e33
                | (have j1 := b26e74 X0
                   grind)
                | exact resolve b26e33 b26e74
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e33
              have b26e16930 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e301 (σ y) (σ y) X0
                   grind)
                | (have i₁ := b26e25
                   have i₂ := b26e301 (σ y) X0 (σ y)
                   grind)
                | exact superpose b26e301 b26e25
                | (have j1 := b26e301 (σ y) x x
                   grind)
                | exact resolve b26e25 b26e301
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e16950 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e74 X0
                   have i₂ := b26e301 X0 X0 X1
                   grind)
                | (have i₁ := b26e74 X0
                   have i₂ := b26e301 X0 X1 X0
                   grind)
                | exact superpose b26e301 b26e74
                | (have j0 := b26e74 X0
                   have j1 := b26e301 X0 X1 x
                   grind)
                | exact resolve b26e74 b26e301
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e74 b26e301
              have b26e17215 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
                intro X0 X1
                first
                | (have j0 := b26e16950 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e16950
              have b26e17240 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have j1 := b26e17215 (σ y) x
                   grind)
                | (have r₁ := b26e16930 x
                   have r₂ := b26e17215 (σ y) x
                   grind)
                | exact resolve b26e16930 b26e17215
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e16930 b26e17215
              have b26e17245 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e17240
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e17240
                | exact resolve b26e17240 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e17240
              have b26e24499 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e17245
                   grind)
                | exact superpose b26e17245 b26e22
                | exact resolve b26e22 b26e17245
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e17245
              have b26e26215 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b26e24499
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e24499
                | (have j1 := b26e20 y y
                   grind)
                | exact resolve b26e24499 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e24499
              have b26e26229 : y = (M.op y y) ∨ x = (M.op x x) := by grind
              clear b26e26215
              have b26e26235 : x = (M.op x x) := by
                first
                | (have r₁ := b26e26229
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e26229 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e26229
              have b26e26236 : False := by grind
              exact b26e26236
