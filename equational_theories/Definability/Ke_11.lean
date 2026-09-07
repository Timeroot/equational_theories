import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_x_pxx_pyx_Equation3587 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b0e11 y x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ x))) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) (σ x) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e34 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e34
        | exact resolve b0e34 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e41 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e33 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e33
        | exact resolve b0e33 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e54 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e40 (σ x)
           grind)
        | exact superpose b0e40 b0e18
        | exact resolve b0e18 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e55 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e54
           have i₂ := b0e41 x
           grind)
        | exact superpose b0e41 b0e54
        | exact resolve b0e54 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e54
      have b0e56 : False := by grind
      exact b0e56
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
        clear b1e27
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
        have b1e41 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b1e12 y y x
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e12
          | exact resolve b1e12 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : ∀ X0 : G, y = (M.op X0 y) := by
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
        clear b1e28 b1e41
        have b1e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b1e150 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e57 y
             grind)
          | exact superpose b1e57 b1e25
          | (have j1 := b1e57 y
             grind)
          | exact resolve b1e25 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e57
        have b1e162 : (σ (M.op x y)) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e150
             have r₂ := b1e24
             grind)
          | exact resolve b1e150 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e150
        have b1e166 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e162
             have i₂ := b1e31
             grind)
          | exact superpose b1e31 b1e162
          | exact resolve b1e162 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e162
        have b1e169 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e166
             have i₂ := b1e47 x
             grind)
          | exact superpose b1e47 b1e166
          | exact resolve b1e166 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e166
        have b1e170 : False := by grind
        exact b1e170
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e28 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b2e12 y x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 (M.op (M.op X0 X1) X1) X3
             have i₂ := b2e12 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e30 X0 X1 x X3
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e30
          | exact resolve b2e30 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e34 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e28 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e28
          | exact resolve b2e28 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e36 : ∀ X0 : G, y ≠ X0 ∨ y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b2e15 y X0
             have i₂ := b2e34 X0
             grind)
          | exact superpose b2e34 b2e15
          | (have j0 := b2e15 y X0
             grind)
          | (have r₁ := b2e15 y y
             have r₂ := b2e34 y
             grind)
          | exact resolve b2e15 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b2e42 : y = (k y y) := by
          first
          | (have j0 := b2e36 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e46 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e152 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e41 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e187 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e46 x y
             grind)
          | exact superpose b2e46 b2e19
          | (have j1 := b2e46 x y
             grind)
          | exact resolve b2e19 b2e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46
        have b2e197 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e187
             have r₂ := b2e22
             grind)
          | exact resolve b2e187 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e187
        have b2e200 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e197
             have i₂ := b2e34 x
             grind)
          | exact superpose b2e34 b2e197
          | exact resolve b2e197 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e197
        have b2e503 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e152 y
             have i₂ := b2e42
             grind)
          | exact superpose b2e42 b2e152
          | (have j0 := b2e152 y
             grind)
          | exact resolve b2e152 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e152
        have b2e506 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e503
        have b2e520 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e32 (σ y) (σ y) x
             have i₂ := b2e506
             grind)
          | exact superpose b2e506 b2e32
          | exact resolve b2e32 b2e506
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e506
        have b2e533 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e200
             have i₂ := b2e17 y x
             grind)
          | exact superpose b2e17 b2e200
          | (have j1 := b2e17 (σ x) (M.op (σ x) (σ y))
             grind)
          | (have r₁ := b2e200
             have r₂ := b2e17 (σ y) (σ (k y x))
             grind)
          | (have r₁ := b2e200
             have r₂ := b2e17 (σ (k y x)) (σ y)
             grind)
          | exact resolve b2e200 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e200
        have b2e534 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e533
             have i₂ := b2e34 x
             grind)
          | exact superpose b2e34 b2e533
          | exact resolve b2e533 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e533
        have b2e535 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
        clear b2e534
        have b2e536 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e535
             have i₂ := b2e520 (σ x)
             grind)
          | exact superpose b2e520 b2e535
          | exact resolve b2e535 b2e520
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e520 b2e535
        have b2e537 : x = y ∨ x = (M.op x y) := by
          first
          | (have r₁ := b2e536
             have r₂ := b2e22
             grind)
          | exact resolve b2e536 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e536
        have b2e538 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e537
             have i₂ := b2e34 x
             grind)
          | exact superpose b2e34 b2e537
          | exact resolve b2e537 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e537
        have b2e539 : x = y := by grind
        clear b2e538
        have b2e543 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e539
             grind)
          | exact superpose b2e539 b2e22
          | exact resolve b2e22 b2e539
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e539
        have b2e546 : False := by grind
        exact b2e546
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
        have b3e53 : y = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b3e32
        have b3e56 : y = (M.op y y) := by grind
        clear b3e53
        have b3e59 : False := by grind
        exact b3e59
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
          have b4e47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b4e147 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e47
          have b4e158 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
          clear b4e147
          have b4e161 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b4e158
          have b4e162 : y = (M.op y y) := by grind
          clear b4e161
          have b4e163 : False := by grind
          exact b4e163
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
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
        have b6e41 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 (M.op (M.op X0 X1) X1) X3
             have i₂ := b6e12 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op (M.op X0 X1) X1) = (k (M.op (M.op X0 X1) X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 (M.op (M.op X0 X1) X1) X2
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 (M.op (M.op X0 X1) X1) X2
             grind)
          | (have r₁ := b6e15 (M.op (M.op X0 X1) X1) (M.op X0 X1)
             have r₂ := b6e12 X0 X1 (M.op X0 X1)
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e41 X0 X1 x X3
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e41
          | exact resolve b6e41 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b6e61 : (σ x) = (σ (M.op y x)) ∨ x = y ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e26
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e26 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e62 : (σ x) = (σ (M.op y x)) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e61
             have r₂ := b6e21
             grind)
          | exact resolve b6e61 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e65 : (σ x) = (σ (M.op y x)) := by
          first
          | (have r₁ := b6e62
             have r₂ := b6e20
             grind)
          | exact resolve b6e62 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e78 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 x
             have i₂ := b6e43 (M.op X0 X1) X1 x
             grind)
          | exact superpose b6e43 b6e12
          | exact resolve b6e12 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e114 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e42 X0 X1 (M.op X0 X1)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e115 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e114 X0 X1
             have i₂ := b6e78 X0 X1
             grind)
          | exact superpose b6e78 b6e114
          | exact resolve b6e114 b6e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78 b6e114
        have b6e141 : (M.op (σ x) (σ x)) = (σ (k (M.op y x) (M.op y x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e53 (M.op y x)
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e53
          | (have j0 := b6e53 x
             grind)
          | exact resolve b6e53 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e148 : (σ (M.op y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e141
             have i₂ := b6e115 y x
             grind)
          | exact superpose b6e115 b6e141
          | exact resolve b6e141 b6e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e115 b6e141
        have b6e149 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e148
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e148
          | exact resolve b6e148 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65 b6e148
        have b6e150 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b6e149
        have b6e184 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e43 (σ x) (σ x) x
             have i₂ := b6e150
             grind)
          | exact superpose b6e150 b6e43
          | exact resolve b6e43 b6e150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e150
        have b6e264 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e184 (σ y)
             grind)
          | exact superpose b6e184 b6e22
          | exact resolve b6e22 b6e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e184
        have b6e298 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e264
             grind)
          | exact superpose b6e264 b6e13
          | exact resolve b6e13 b6e264
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e264
        have b6e311 : x = y := by
          first
          | (have i₁ := b6e298
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e298
          | exact resolve b6e298 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e298
        have b6e315 : False := by grind
        exact b6e315
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
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
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
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b8e29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b8e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e29 X0 X1 x X3
               have i₂ := b8e13 X0 X1 x
               grind)
            | exact superpose b8e13 b8e29
            | exact resolve b8e29 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29
          have b8e36 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 X1 x
               have i₂ := b8e31 (M.op X0 X1) X1 x
               grind)
            | exact superpose b8e31 b8e13
            | exact resolve b8e13 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e38 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 (M.op X0 X1) X2
               have i₂ := b8e31 X0 X1 X2
               grind)
            | exact superpose b8e31 b8e16
            | (have j0 := b8e16 (M.op X0 X1) X2
               grind)
            | (have r₁ := b8e16 (M.op X0 X1) (M.op X0 X1)
               have r₂ := b8e31 X0 X1 (M.op X0 X1)
               grind)
            | exact resolve b8e16 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b8e52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (M.op X0 X1)
               have i₂ := b8e36 X0 X1
               grind)
            | exact superpose b8e36 b8e16
            | (have j0 := b8e16 X1 (M.op X0 X1)
               grind)
            | (have r₁ := b8e16 X1 (M.op X0 X1)
               have r₂ := b8e36 X0 X1
               grind)
            | exact resolve b8e16 b8e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e55 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e66 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
          have b8e70 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e86 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e27 X0 X1
               have i₂ := b8e18 X1 (τ X0)
               grind)
            | exact superpose b8e18 b8e27
            | (have j1 := b8e18 (k (σ X1) X0) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e27 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e91 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e123 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e91 X0 (M.op X1 (σ X0))
               have i₂ := b8e55 X1 (σ X0)
               grind)
            | exact superpose b8e55 b8e91
            | exact resolve b8e91 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55 b8e91
          have b8e135 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e123 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e123
            | exact resolve b8e123 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e149 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e176 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          have b8e181 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e31 (σ X0) (σ X1) x
               have i₂ := b8e57 X0 X1
               grind)
            | exact superpose b8e57 b8e31
            | (have j1 := b8e57 X0 X1
               grind)
            | exact resolve b8e31 b8e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57
          have b8e188 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e176
               have r₂ := b8e24
               grind)
            | exact resolve b8e176 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e176
          have b8e504 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e149 (τ X0)
               have i₂ := b8e27 X0 (τ X0)
               grind)
            | exact superpose b8e27 b8e149
            | (have j0 := b8e149 (τ X0)
               grind)
            | exact resolve b8e149 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e149
          have b8e506 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e504 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e504
            | (have j0 := b8e504 X0
               grind)
            | exact resolve b8e504 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e504
          have b8e509 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e506 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e506
            | (have j0 := b8e506 X0
               grind)
            | exact resolve b8e506 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e506
          have b8e519 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e188
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e188
            | (have j1 := b8e18 (σ x) (M.op (σ x) (σ y))
               grind)
            | (have r₁ := b8e188
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e188
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e188 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e188
          have b8e520 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b8e519
          have b8e521 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e520
               have r₂ := b8e22
               grind)
            | exact resolve b8e520 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e520
          have b8e524 : y = (k y (τ (σ x))) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e135 y (σ x)
               have i₂ := b8e521
               grind)
            | exact superpose b8e521 b8e135
            | exact resolve b8e135 b8e521
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135 b8e521
          have b8e538 : y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e524
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e524
            | exact resolve b8e524 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e524
          have b8e540 : y = (k y x) := by
            first
            | (have j1 := b8e16 y x
               grind)
            | (have r₁ := b8e538
               have r₂ := b8e16 y x
               grind)
            | exact resolve b8e538 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e538
          have b8e622 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e66 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e66
            | exact resolve b8e66 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e657 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e622 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e622
            | (have j0 := b8e622 X0 X1
               grind)
            | exact resolve b8e622 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e622
          have b8e722 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (σ (M.op X0 X1)) X2) ∨ (M.op X0 X1) = (τ X2) ∨ (M.op X0 X1) = (τ X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e86 X0 (M.op X0 X1)
               have i₂ := b8e31 X0 X1 (τ X0)
               grind)
            | exact superpose b8e31 b8e86
            | (have j0 := b8e86 X2 (M.op X0 X1)
               grind)
            | exact resolve b8e86 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e753 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (σ (M.op X0 X1)) X2) ∨ (M.op X0 X1) = (τ X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e722 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e722
          have b8e816 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e181 y x x
               have i₂ := b8e540
               grind)
            | exact superpose b8e540 b8e181
            | (have j0 := b8e181 x y x
               grind)
            | exact resolve b8e181 b8e540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e181
          have b8e843 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b8e816 X0
               grind)
            | (have r₁ := b8e816 X0
               have r₂ := b8e24
               grind)
            | exact resolve b8e816 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e816
          have b8e2307 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e657 y x
               have i₂ := b8e540
               grind)
            | exact superpose b8e540 b8e657
            | (have j0 := b8e657 (σ (M.op x y)) (σ y)
               grind)
            | exact resolve b8e657 b8e540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e540 b8e657
          have b8e2366 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e2307
               have r₂ := b8e22
               grind)
            | exact resolve b8e2307 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2307
          have b8e2509 : ∀ X0 X1 X2 : G, (τ (σ (M.op X0 X1))) = (k (τ (σ (M.op X0 X1))) X2) ∨ (M.op X0 X1) = (τ (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e70 (σ (M.op X0 X1)) X2
               have i₂ := b8e753 X0 X1 (σ X2)
               grind)
            | exact superpose b8e753 b8e70
            | (have j1 := b8e753 X0 X1 (σ X2)
               grind)
            | exact resolve b8e70 b8e753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e753
          have b8e2525 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = (τ (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e2509 X0 X1 X2
               have i₂ := b8e14 (M.op X0 X1)
               grind)
            | exact superpose b8e14 b8e2509
            | (have j0 := b8e2509 X0 X1 X2
               grind)
            | exact resolve b8e2509 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2509
          have b8e2544 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e2525 X0 X1 X2
               have i₂ := b8e14 X2
               grind)
            | exact superpose b8e14 b8e2525
            | (have j0 := b8e2525 X0 X1 X2
               grind)
            | exact resolve b8e2525 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2525
          have b8e2552 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e2544 X0 X1 (k (M.op X0 X1) X2)
               have j1 := b8e38 X0 X1 X2
               grind)
            | (have r₁ := b8e2544 X0 X1 X2
               have r₂ := b8e38 X0 X1 X2
               grind)
            | (have r₁ := b8e2544 X0 X1 (M.op X0 X1)
               have r₂ := b8e38 X0 X1 (M.op X0 X1)
               grind)
            | (have r₁ := b8e2544 X0 X1 X2
               have r₂ := b8e38 X0 X1 (k (M.op X0 X1) X2)
               grind)
            | exact resolve b8e2544 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38 b8e2544
          have b8e4073 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (k (τ (M.op X0 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e70 (M.op X0 X1) X2
               have i₂ := b8e2552 X0 X1 (σ X2)
               grind)
            | exact superpose b8e2552 b8e70
            | exact resolve b8e70 b8e2552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
          have b8e4074 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (σ (M.op X0 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e27 X2 (M.op X0 X1)
               have i₂ := b8e2552 X0 X1 (τ X2)
               grind)
            | exact superpose b8e2552 b8e27
            | exact resolve b8e27 b8e2552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27 b8e2552
          have b8e6451 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e509 (τ (M.op X0 X1))
               have i₂ := b8e4073 X0 X1 (τ (M.op X0 X1))
               grind)
            | exact superpose b8e4073 b8e509
            | (have j0 := b8e509 (τ (M.op X0 X1))
               grind)
            | (have r₁ := b8e509 (τ (M.op X0 X1))
               have r₂ := b8e4073 X0 X1 (τ (M.op X0 X1))
               grind)
            | exact resolve b8e509 b8e4073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4073
          have b8e6486 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b8e6451 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6451
          have b8e9204 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e4074 x y x
               have i₂ := b8e2366
               grind)
            | exact superpose b8e2366 b8e4074
            | exact resolve b8e4074 b8e2366
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4074
          have b8e9328 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e509 (σ y)
               have i₂ := b8e9204 (σ y)
               grind)
            | exact superpose b8e9204 b8e509
            | (have j0 := b8e509 (σ y)
               grind)
            | (have r₁ := b8e509 (σ y)
               have r₂ := b8e9204 (σ y)
               grind)
            | exact resolve b8e509 b8e9204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e509 b8e9204
          have b8e9369 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e9328
          have b8e19086 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e31 (σ y) (σ y) x
               have i₂ := b8e9369
               grind)
            | exact superpose b8e9369 b8e31
            | exact resolve b8e31 b8e9369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9369
          have b8e19390 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e19086 (σ x)
               grind)
            | exact superpose b8e19086 b8e20
            | exact resolve b8e20 b8e19086
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19086
          have b8e19408 : x = (M.op x y) := by
            first
            | (have r₁ := b8e19390
               have r₂ := b8e2366
               grind)
            | exact resolve b8e19390 b8e2366
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2366 b8e19390
          have b8e32425 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e31 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
               have i₂ := b8e6486 X0 X1
               grind)
            | exact superpose b8e6486 b8e31
            | exact resolve b8e31 b8e6486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31 b8e6486
          have b8e48522 : ∀ X1 : G, (τ (σ y)) = (M.op X1 (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X1
            first
            | (have i₁ := b8e32425 x (σ y) x
               have i₂ := b8e843 x
               grind)
            | exact superpose b8e843 b8e32425
            | exact resolve b8e32425 b8e843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32425
          have b8e48546 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e20
               have i₂ := b8e843 X0
               grind)
            | exact superpose b8e843 b8e20
            | (have j1 := b8e843 X0
               grind)
            | exact resolve b8e20 b8e843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e843
          have b8e48609 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e48546 X0
               have i₂ := b8e19408
               grind)
            | exact superpose b8e19408 b8e48546
            | (have j0 := b8e48546 X0
               grind)
            | exact resolve b8e48546 b8e19408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48546
          have b8e48610 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e48609 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48609
          have b8e48620 : ∀ X1 : G, y = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X1
            first
            | (have i₁ := b8e48522 X1
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e48522
            | exact resolve b8e48522 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48522
          have b8e48638 : ∀ X1 : G, (σ x) = (σ y) ∨ y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b8e48620 X1
               have i₂ := b8e48610 (σ x)
               grind)
            | exact superpose b8e48610 b8e48620
            | (have j0 := b8e48620 X1
               grind)
            | exact resolve b8e48620 b8e48610
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48610 b8e48620
          have b8e48654 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have j0 := b8e48638 X1
               grind)
            | (have r₁ := b8e48638 X1
               have r₂ := b8e24
               grind)
            | exact resolve b8e48638 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48638
          have b8e49947 : x = y := by
            first
            | (have i₁ := b8e19408
               have i₂ := b8e48654 x
               grind)
            | exact superpose b8e48654 b8e19408
            | exact resolve b8e19408 b8e48654
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19408 b8e48654
          have b8e49963 : False := by grind
          exact b8e49963

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_y_pyx_Equation3600 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op x x) := by grind
        have b0e21 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b0e22 : x = (M.op y y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e38 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b0e12 x x x
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e45 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X0 (M.op y x) X1
             have i₂ := b0e38 (M.op (M.op y x) X0)
             grind)
          | exact superpose b0e38 b0e12
          | exact resolve b0e12 b0e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e46 : ∀ X1 : G, y = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b0e45 x X1
             have i₂ := b0e38 x
             grind)
          | exact superpose b0e38 b0e45
          | exact resolve b0e45 b0e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38 b0e45
        have b0e60 : x = y := by
          first
          | (have i₁ := b0e22
             have i₂ := b0e46 y
             grind)
          | exact superpose b0e46 b0e22
          | exact resolve b0e22 b0e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e46
        have b0e90 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e60
             grind)
          | exact superpose b0e60 b0e19
          | exact resolve b0e19 b0e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e60
        have b0e97 : (σ y) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e90
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e90
          | exact resolve b0e90 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e90
        have b0e98 : False := by grind
        exact b0e98
      · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b1e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e20
            | exact resolve b1e20 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b1e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e44 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b1e42 X0 X1 x X3
               have i₂ := b1e13 X0 X1 x
               grind)
            | exact superpose b1e13 b1e42
            | exact resolve b1e42 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e42
          have b1e102 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b1e44 (σ x) (σ x) x
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e44
            | exact resolve b1e44 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e44
          have b1e163 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b1e26
               have i₂ := b1e102 (σ x)
               grind)
            | exact superpose b1e102 b1e26
            | (have r₁ := b1e26
               have r₂ := b1e102 (σ x)
               grind)
            | exact resolve b1e26 b1e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e26 b1e102
          have b1e164 : False := by grind
          exact b1e164
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b2e21 : y = (M.op x x) := by grind
          have b2e24 : y ≠ (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e37 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b2e13 x x x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e45 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X0 (M.op y x) X1
               have i₂ := b2e37 (M.op (M.op y x) X0)
               grind)
            | exact superpose b2e37 b2e13
            | exact resolve b2e13 b2e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e46 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b2e45 x X1
               have i₂ := b2e37 x
               grind)
            | exact superpose b2e37 b2e45
            | exact resolve b2e45 b2e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e37 b2e45
          have b2e58 : y ≠ y := by
            first
            | (have i₁ := b2e24
               have i₂ := b2e46 x
               grind)
            | exact superpose b2e46 b2e24
            | (have r₁ := b2e24
               have r₂ := b2e46 x
               grind)
            | exact resolve b2e24 b2e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e46
          have b2e60 : False := by grind
          exact b2e60
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : y = (M.op x x) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b3e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : x = (k x y) := by grind
          have b3e32 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b3e13 x x x
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e13
            | exact resolve b3e13 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e39 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b3e13 X0 (M.op y x) X1
               have i₂ := b3e32 (M.op (M.op y x) X0)
               grind)
            | exact superpose b3e32 b3e13
            | exact resolve b3e13 b3e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e40 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b3e39 x X1
               have i₂ := b3e32 x
               grind)
            | exact superpose b3e32 b3e39
            | exact resolve b3e39 b3e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e32 b3e39
          have b3e44 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b3e47 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b3e44
          have b3e48 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e47
               have r₂ := b3e22
               grind)
            | exact resolve b3e47 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e47
          have b3e51 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b3e48
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e48
            | exact resolve b3e48 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e48
          have b3e52 : (σ x) = (σ y) := by
            first
            | (have i₁ := b3e51
               have i₂ := b3e26
               grind)
            | exact superpose b3e26 b3e51
            | exact resolve b3e51 b3e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26 b3e51
          have b3e53 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e52
               grind)
            | exact superpose b3e52 b3e20
            | exact resolve b3e20 b3e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e54 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e23
               have i₂ := b3e52
               grind)
            | exact superpose b3e52 b3e23
            | exact resolve b3e23 b3e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e61 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e53
               have i₂ := b3e54
               grind)
            | exact superpose b3e54 b3e53
            | exact resolve b3e53 b3e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e53 b3e54
          have b3e62 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e61
               have i₂ := b3e40 x
               grind)
            | exact superpose b3e40 b3e61
            | exact resolve b3e61 b3e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e40 b3e61
          have b3e63 : False := by grind
          exact b3e63
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b4e22 : y = (M.op x x) := by grind
            have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b4e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b4e21
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e21
              | exact resolve b4e21 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e29 : x = (k x y) := by grind
            have b4e46 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b4e49 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b4e46
            have b4e53 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e49
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e49 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e49
            have b4e55 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b4e53
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e53
              | exact resolve b4e53 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e53
            have b4e56 : (σ x) = (σ y) := by
              first
              | (have i₁ := b4e55
                 have i₂ := b4e29
                 grind)
              | exact superpose b4e29 b4e55
              | exact resolve b4e55 b4e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e29 b4e55
            have b4e76 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b4e28
                 have i₂ := b4e56
                 grind)
              | exact superpose b4e56 b4e28
              | exact resolve b4e28 b4e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e28
            have b4e77 : (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b4e24
                 have i₂ := b4e56
                 grind)
              | exact superpose b4e56 b4e24
              | exact resolve b4e24 b4e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e56
            have b4e84 : False := by grind
            exact b4e84
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b5e22 : y = (M.op x x) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b5e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : x = (k x y) := by grind
            have b5e31 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
              intro X0
              first
              | (have i₁ := b5e14 x x x
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e39 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X0 (M.op y x) X1
                 have i₂ := b5e31 (M.op (M.op y x) X0)
                 grind)
              | exact superpose b5e31 b5e14
              | exact resolve b5e14 b5e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e40 : ∀ X1 : G, y = (M.op X1 y) := by
              intro X1
              first
              | (have i₁ := b5e39 x X1
                 have i₂ := b5e31 x
                 grind)
              | exact superpose b5e31 b5e39
              | exact resolve b5e39 b5e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e31 b5e39
            have b5e43 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b5e46 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b5e43
            have b5e49 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e46
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e46 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e46
            have b5e50 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b5e49
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e49
              | exact resolve b5e49 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e49
            have b5e51 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e50
                 have i₂ := b5e28
                 grind)
              | exact superpose b5e28 b5e50
              | exact resolve b5e50 b5e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e28 b5e50
            have b5e52 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b5e21
                 have i₂ := b5e51
                 grind)
              | exact superpose b5e51 b5e21
              | exact resolve b5e21 b5e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e53 : (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b5e24
                 have i₂ := b5e51
                 grind)
              | exact superpose b5e51 b5e24
              | exact resolve b5e24 b5e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e60 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b5e52
                 have i₂ := b5e53
                 grind)
              | exact superpose b5e53 b5e52
              | exact resolve b5e52 b5e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e52 b5e53
            have b5e61 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b5e60
                 have i₂ := b5e40 x
                 grind)
              | exact superpose b5e40 b5e60
              | exact resolve b5e60 b5e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e40 b5e60
            have b5e62 : False := by grind
            exact b5e62
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op x x) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b6e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e30 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b6e13 x x x
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e38 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 X0 (M.op y x) X1
               have i₂ := b6e30 (M.op (M.op y x) X0)
               grind)
            | exact superpose b6e30 b6e13
            | exact resolve b6e13 b6e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e39 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b6e38 x X1
               have i₂ := b6e30 x
               grind)
            | exact superpose b6e30 b6e38
            | exact resolve b6e38 b6e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e30 b6e38
          have b6e48 : y = (k y y) := by grind
          have b6e52 : x = y := by
            first
            | (have i₁ := b6e24
               have i₂ := b6e39 y
               grind)
            | exact superpose b6e39 b6e24
            | exact resolve b6e24 b6e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e39
          have b6e56 : x = (k x x) := by
            first
            | (have i₁ := b6e48
               have i₂ := b6e52
               grind)
            | exact superpose b6e52 b6e48
            | exact resolve b6e48 b6e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e48
          have b6e72 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e22
               have i₂ := b6e18 (σ x) X0
               grind)
            | (have i₁ := b6e22
               have i₂ := b6e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b6e18 b6e22
            | (have j1 := b6e18 (σ x) X0
               grind)
            | (have r₁ := b6e22
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e22 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e77 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e72 X0
               have i₂ := b6e52
               grind)
            | exact superpose b6e52 b6e72
            | (have j0 := b6e72 X0
               grind)
            | exact resolve b6e72 b6e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e72
          have b6e80 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e52
               grind)
            | exact superpose b6e52 b6e23
            | exact resolve b6e23 b6e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e52
          have b6e606 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have j0 := b6e77 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e77
          have b6e607 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
            first
            | (have r₁ := b6e606
               have r₂ := b6e80
               grind)
            | exact resolve b6e606 b6e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e606
          have b6e608 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
            first
            | (have i₁ := b6e607
               have i₂ := b6e19 x x
               grind)
            | exact superpose b6e19 b6e607
            | exact resolve b6e607 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e607
          have b6e609 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e608
               have i₂ := b6e56
               grind)
            | exact superpose b6e56 b6e608
            | exact resolve b6e608 b6e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e56 b6e608
          have b6e610 : False := by grind
          exact b6e610
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e22 : y = (M.op x x) := by grind
            have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b7e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e29 : x = (k x y) := by grind
            have b7e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b7e23
                 have i₂ := b7e19 (σ x) X0
                 grind)
              | (have i₁ := b7e23
                 have i₂ := b7e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b7e19 b7e23
              | (have j1 := b7e19 (σ x) X0
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e19 (σ x) (σ y)
                 grind)
              | exact resolve b7e23 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e530 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b7e65 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e65
            have b7e531 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b7e530
                 have r₂ := b7e24
                 grind)
              | exact resolve b7e530 b7e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e530
            have b7e532 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b7e531
                 have i₂ := b7e20 x y
                 grind)
              | exact superpose b7e20 b7e531
              | exact resolve b7e531 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e531
            have b7e533 : (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b7e532
                 have i₂ := b7e29
                 grind)
              | exact superpose b7e29 b7e532
              | exact resolve b7e532 b7e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e29 b7e532
            have b7e534 : False := by grind
            exact b7e534
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b8e22 : y = (M.op x x) := by grind
            have b8e26 : y ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e31 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
              intro X0
              first
              | (have i₁ := b8e14 x x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e38 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X0 (M.op y x) X1
                 have i₂ := b8e31 (M.op (M.op y x) X0)
                 grind)
              | exact superpose b8e31 b8e14
              | exact resolve b8e14 b8e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e39 : ∀ X1 : G, y = (M.op X1 y) := by
              intro X1
              first
              | (have i₁ := b8e38 x X1
                 have i₂ := b8e31 x
                 grind)
              | exact superpose b8e31 b8e38
              | exact resolve b8e38 b8e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e31 b8e38
            have b8e50 : y ≠ y := by
              first
              | (have i₁ := b8e26
                 have i₂ := b8e39 x
                 grind)
              | exact superpose b8e39 b8e26
              | (have r₁ := b8e26
                 have r₂ := b8e39 x
                 grind)
              | exact resolve b8e26 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e39
            have b8e52 : False := by grind
            exact b8e52
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : y ≠ (M.op x x) := by grind
          have b9e22 : x = (M.op y x) := by grind
          have b9e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b9e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e27 : (σ x) = (k (σ x) (σ y)) := by grind
          have b9e28 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b9e27
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e27
            | exact resolve b9e27 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e27
          have b9e29 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b9e14 (k x y)
               have i₂ := b9e28
               grind)
            | exact superpose b9e28 b9e14
            | exact resolve b9e14 b9e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e28
          have b9e30 : x = (k x y) := by
            first
            | (have i₁ := b9e29
               have i₂ := b9e14 x
               grind)
            | exact superpose b9e14 b9e29
            | exact resolve b9e29 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e29
          have b9e43 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b9e13 x y X0
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e13
            | exact resolve b9e13 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e44 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b9e13 y y x
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e13
            | exact resolve b9e13 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e47 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b9e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b9e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e49 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b9e47 X0 X1 x X3
               have i₂ := b9e13 X0 X1 x
               grind)
            | exact superpose b9e13 b9e47
            | exact resolve b9e47 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e47
          have b9e50 : x = (M.op x y) := by
            first
            | (have i₁ := b9e43 x
               have i₂ := b9e44 x
               grind)
            | exact superpose b9e44 b9e43
            | exact resolve b9e43 b9e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e43 b9e44
          have b9e51 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b9e13 y x X0
               have i₂ := b9e50
               grind)
            | exact superpose b9e50 b9e13
            | exact resolve b9e13 b9e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e50
          have b9e52 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b9e51 x
               have i₂ := b9e49 x x x
               grind)
            | exact superpose b9e49 b9e51
            | exact resolve b9e51 b9e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e49 b9e51
          have b9e53 : x = (M.op x x) := by
            first
            | (have i₁ := b9e52
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e52
            | exact resolve b9e52 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e52
          have b9e57 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b9e59 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b9e57
          have b9e60 : y = (k x y) := by
            first
            | (have r₁ := b9e59
               have r₂ := b9e21
               grind)
            | exact resolve b9e59 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e59
          have b9e62 : x = y := by
            first
            | (have i₁ := b9e60
               have i₂ := b9e30
               grind)
            | exact superpose b9e30 b9e60
            | exact resolve b9e60 b9e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e30 b9e60
          have b9e63 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e62
               grind)
            | exact superpose b9e62 b9e20
            | exact resolve b9e20 b9e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e70 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e63
               have i₂ := b9e53
               grind)
            | exact superpose b9e53 b9e63
            | exact resolve b9e63 b9e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e53 b9e63
          have b9e71 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b9e70
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e70
            | exact resolve b9e70 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e70
          have b9e72 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b9e71
               have i₂ := b9e62
               grind)
            | exact superpose b9e62 b9e71
            | exact resolve b9e71 b9e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e62 b9e71
          have b9e73 : False := by grind
          exact b9e73
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e22 : y ≠ (M.op x x) := by grind
            have b10e23 : x = (M.op y x) := by grind
            have b10e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b10e25 : x ≠ (M.op y y) := by grind
            have b10e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e29 : (σ x) = (k (σ x) (σ y)) := by grind
            have b10e30 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b10e29
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e29
              | exact resolve b10e29 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e29
            have b10e31 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e30
                 grind)
              | exact superpose b10e30 b10e15
              | exact resolve b10e15 b10e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e30
            have b10e32 : x = (k x y) := by
              first
              | (have i₁ := b10e31
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e31
              | exact resolve b10e31 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e31
            have b10e48 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b10e14 x y X0
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e14
              | exact resolve b10e14 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e52 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b10e48 X0
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e48
              | exact resolve b10e48 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e48
            have b10e54 : x ≠ y := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e52 y
                 grind)
              | exact superpose b10e52 b10e25
              | exact resolve b10e25 b10e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e52
            have b10e63 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
            have b10e64 : y = (M.op x x) ∨ y = (k x y) := by grind
            clear b10e63
            have b10e67 : y = (k x y) := by
              first
              | (have r₁ := b10e64
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e64 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e64
            have b10e71 : x = y := by
              first
              | (have i₁ := b10e67
                 have i₂ := b10e32
                 grind)
              | exact superpose b10e32 b10e67
              | exact resolve b10e67 b10e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e32 b10e67
            have b10e72 : False := by grind
            exact b10e72
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op x x) := by grind
            have b11e23 : x = (M.op y x) := by grind
            have b11e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b11e26 : y ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e28 : (σ x) = (k (σ x) (σ y)) := by grind
            have b11e29 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b11e28
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e28
              | exact resolve b11e28 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e28
            have b11e30 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e29
                 grind)
              | exact superpose b11e29 b11e15
              | exact resolve b11e15 b11e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e29
            have b11e31 : x = (k x y) := by
              first
              | (have i₁ := b11e30
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e30
              | exact resolve b11e30 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e30
            have b11e54 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
            have b11e59 : y = (M.op x x) ∨ y = (k x y) := by grind
            clear b11e54
            have b11e62 : y = (k x y) := by
              first
              | (have r₁ := b11e59
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e59 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e59
            have b11e63 : x = y := by
              first
              | (have i₁ := b11e62
                 have i₂ := b11e31
                 grind)
              | exact superpose b11e31 b11e62
              | exact resolve b11e62 b11e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e31 b11e62
            have b11e65 : x = (M.op x x) := by
              first
              | (have i₁ := b11e23
                 have i₂ := b11e63
                 grind)
              | exact superpose b11e63 b11e23
              | exact resolve b11e23 b11e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e67 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b11e26
                 have i₂ := b11e63
                 grind)
              | exact superpose b11e63 b11e26
              | exact resolve b11e26 b11e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e63
            have b11e71 : False := by grind
            exact b11e71
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b12e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b12e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b12e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b12e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b12e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e23 : x = (M.op y x) := by grind
            have b12e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b12e25 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b12e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : y = (k y x) := by grind
            have b12e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e20 (τ X0) X1
                 have i₂ := b12e16 X0
                 grind)
              | exact superpose b12e16 b12e20
              | exact resolve b12e20 b12e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e31 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b12e14 x y X0
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e14
              | exact resolve b12e14 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e32 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b12e14 y y x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e14 X2 (M.op (M.op X1 X0) X1) X3
                 have i₂ := b12e14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b12e35 X0 X1 x X3
                 have i₂ := b12e14 X0 X1 x
                 grind)
              | exact superpose b12e14 b12e35
              | exact resolve b12e35 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e35
            have b12e38 : x = (M.op x y) := by
              first
              | (have i₁ := b12e31 x
                 have i₂ := b12e32 x
                 grind)
              | exact superpose b12e32 b12e31
              | exact resolve b12e31 b12e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e31 b12e32
            have b12e58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e20 X1 X0
                 have i₂ := b12e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b12e19 b12e20
              | (have j1 := b12e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b12e20 b12e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e90 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b12e37 (σ y) (σ x) x
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e37
              | exact resolve b12e37 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e98 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X1 X0 x
                 have i₂ := b12e37 (M.op X0 X1) X0 x
                 grind)
              | exact superpose b12e37 b12e14
              | exact resolve b12e14 b12e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e103 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e18 (M.op X0 X1) X2
                 have i₂ := b12e37 X0 X1 X2
                 grind)
              | exact superpose b12e37 b12e18
              | (have j0 := b12e18 (M.op X0 X1) X2
                 grind)
              | (have r₁ := b12e18 (M.op X0 X1) x
                 have r₂ := b12e37 X0 X1 x
                 grind)
              | exact resolve b12e18 b12e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e105 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have j0 := b12e103 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e103
            have b12e106 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 ∨ (M.op X0 X1) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e105 X0 X1 X2
                 have i₂ := b12e37 X0 X1 (M.op X0 X1)
                 grind)
              | exact superpose b12e37 b12e105
              | (have j0 := b12e105 X0 X1 X2
                 grind)
              | exact resolve b12e105 b12e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e37 b12e105
            have b12e118 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
              intro X0
              grind
            clear b12e29
            have b12e123 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
              intro X0
              first
              | (have i₁ := b12e118 X0
                 have i₂ := b12e16 X0
                 grind)
              | exact superpose b12e16 b12e118
              | exact resolve b12e118 b12e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e118
            have b12e138 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b12e24
                 have i₂ := b12e90 (σ x)
                 grind)
              | exact superpose b12e90 b12e24
              | exact resolve b12e24 b12e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e90
            have b12e721 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b12e58 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e58
            have b12e1009 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
              intro X0 X1
              first
              | (have i₁ := b12e123 (M.op X0 X1)
                 have i₂ := b12e106 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                 grind)
              | exact superpose b12e106 b12e123
              | (have j1 := b12e106 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                 grind)
              | exact resolve b12e123 b12e106
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e106 b12e123
            have b12e1011 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
              intro X0 X1
              first
              | (have j0 := b12e1009 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1009
            have b12e2581 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e721 x y
                 have i₂ := b12e28
                 grind)
              | exact superpose b12e28 b12e721
              | (have j0 := b12e721 x y
                 grind)
              | exact resolve b12e721 b12e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28 b12e721
            have b12e2591 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
            clear b12e2581
            have b12e20544 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e98 (σ y) (σ y)
                 have i₂ := b12e2591
                 grind)
              | exact superpose b12e2591 b12e98
              | exact resolve b12e98 b12e2591
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e98 b12e2591
            have b12e509368 : (σ y) = (σ (M.op (τ (σ y)) (τ (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e1011 (σ x) (σ y)
                 have i₂ := b12e20544
                 grind)
              | exact superpose b12e20544 b12e1011
              | exact resolve b12e1011 b12e20544
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1011 b12e20544
            have b12e509395 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e509368
                 have i₂ := b12e15 y
                 grind)
              | exact superpose b12e15 b12e509368
              | exact resolve b12e509368 b12e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e509368
            have b12e509399 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e509395
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e509395
              | exact resolve b12e509395 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e509395
            have b12e509401 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have r₁ := b12e509399
                 have r₂ := b12e138
                 grind)
              | exact resolve b12e509399 b12e138
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e138 b12e509399
            have b12e509450 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e509401
                 grind)
              | exact superpose b12e509401 b12e21
              | exact resolve b12e21 b12e509401
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e509401
            have b12e509605 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b12e509450
                 have i₂ := b12e38
                 grind)
              | exact superpose b12e38 b12e509450
              | exact resolve b12e509450 b12e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e38 b12e509450
            have b12e509606 : False := by grind
            exact b12e509606
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b13e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b13e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e24 : x = (M.op y x) := by grind
              have b13e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : (σ y) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e22
                | exact resolve b13e22 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e36 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
                intro X0
                first
                | (have i₁ := b13e15 x y X0
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b13e15 X2 (M.op (M.op X1 X0) X1) X3
                   have i₂ := b13e15 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e39 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b13e37 X0 X1 x X3
                   have i₂ := b13e15 X0 X1 x
                   grind)
                | exact superpose b13e15 b13e37
                | exact resolve b13e37 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e37
              have b13e40 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b13e36 X0
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e36
                | exact resolve b13e36 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e36
              have b13e43 : y = (k y y) := by grind
              clear b13e40
              have b13e65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b13e21 X1 X0
                   have i₂ := b13e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b13e20 b13e21
                | (have j1 := b13e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b13e21 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e673 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b13e65 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e65
              have b13e675 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b13e673 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e673
              have b13e1444 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b13e675 y
                   have i₂ := b13e43
                   grind)
                | exact superpose b13e43 b13e675
                | (have j0 := b13e675 y
                   grind)
                | exact resolve b13e675 b13e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e43 b13e675
              have b13e1448 : (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b13e1444
              have b13e1473 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b13e39 (σ y) (σ y) x
                   have i₂ := b13e1448
                   grind)
                | exact superpose b13e1448 b13e39
                | exact resolve b13e39 b13e1448
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e39 b13e1448
              have b13e1605 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b13e30
                   have i₂ := b13e1473 (σ x)
                   grind)
                | exact superpose b13e1473 b13e30
                | (have r₁ := b13e30
                   have r₂ := b13e1473 (σ x)
                   grind)
                | exact resolve b13e30 b13e1473
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e30 b13e1473
              have b13e1628 : False := by grind
              exact b13e1628
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e27 : x ≠ (M.op y y) := by grind
              have b14e28 : y ≠ (M.op x y) := by grind
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
              have b14e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
              have b14e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X2 (M.op (M.op X1 X0) X1) X3
                   have i₂ := b14e15 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b14e35 X0 X1 x X3
                   have i₂ := b14e15 X0 X1 x
                   grind)
                | exact superpose b14e15 b14e35
                | exact resolve b14e35 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e35
              have b14e61 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b14e80 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e19 (M.op X0 X1) X2
                   have i₂ := b14e37 X0 X1 X2
                   grind)
                | exact superpose b14e37 b14e19
                | (have j0 := b14e19 (M.op X0 X1) X2
                   grind)
                | (have r₁ := b14e19 (M.op X0 X1) x
                   have r₂ := b14e37 X0 X1 x
                   grind)
                | exact resolve b14e19 b14e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e82 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b14e80 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e80
              have b14e83 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 ∨ (M.op X0 X1) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e82 X0 X1 X2
                   have i₂ := b14e37 X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b14e37 b14e82
                | (have j0 := b14e82 X0 X1 X2
                   grind)
                | exact resolve b14e82 b14e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e82
              have b14e86 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
                intro X0
                grind
              clear b14e30
              have b14e91 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e86 X0
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e86
                | exact resolve b14e86 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e86
              have b14e102 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e31 X0 X1
                   have i₂ := b14e20 X1 (τ X0)
                   grind)
                | exact superpose b14e20 b14e31
                | (have j1 := b14e20 X1 (τ X0)
                   grind)
                | exact resolve b14e31 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e31
              have b14e345 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e61 (σ X1) (σ X0)
                   have i₂ := b14e21 X0 X1
                   grind)
                | exact superpose b14e21 b14e61
                | (have j0 := b14e61 (σ X1) (σ X0)
                   grind)
                | exact resolve b14e61 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e61
              have b14e1027 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b14e91 (M.op X0 X1)
                   have i₂ := b14e83 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   grind)
                | exact superpose b14e83 b14e91
                | (have j1 := b14e83 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   grind)
                | exact resolve b14e91 b14e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e83 b14e91
              have b14e1031 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have j0 := b14e1027 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1027
              have b14e1967 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e102 (σ X0) X1
                   have i₂ := b14e16 X0
                   grind)
                | exact superpose b14e16 b14e102
                | exact resolve b14e102 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e102
              have b14e2068 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e1967 X0 X1
                   have i₂ := b14e21 X1 X0
                   grind)
                | exact superpose b14e21 b14e1967
                | (have j0 := b14e1967 X0 X1
                   grind)
                | exact resolve b14e1967 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1967
              have b14e3064 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e345 y x
                   grind)
                | exact superpose b14e345 b14e22
                | (have j1 := b14e345 y x
                   grind)
                | exact resolve b14e22 b14e345
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e345
              have b14e17626 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b14e16 (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))
                   have i₂ := b14e1031 X0 X1
                   grind)
                | exact superpose b14e1031 b14e16
                | exact resolve b14e16 b14e1031
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1031
              have b14e30354 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e37 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
                   have i₂ := b14e17626 X0 X1
                   grind)
                | exact superpose b14e17626 b14e37
                | exact resolve b14e37 b14e17626
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e37 b14e17626
              have b14e73888 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b14e3064
                   have i₂ := b14e2068 x y
                   grind)
                | exact superpose b14e2068 b14e3064
                | (have j1 := b14e2068 x y
                   grind)
                | (have r₁ := b14e3064
                   have r₂ := b14e2068 x y
                   grind)
                | exact resolve b14e3064 b14e2068
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e2068 b14e3064
              have b14e73892 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
              clear b14e73888
              have b14e73906 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
                first
                | (have r₁ := b14e73892
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e73892 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e73892
              have b14e73917 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
                first
                | (have r₁ := b14e73906
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e73906 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e73906
              have b14e371055 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
                intro X0
                first
                | (have i₁ := b14e30354 (σ x) (σ y) x
                   have i₂ := b14e73917
                   grind)
                | exact superpose b14e73917 b14e30354
                | exact resolve b14e30354 b14e73917
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e30354 b14e73917
              have b14e371062 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) := by
                intro X0
                first
                | (have i₁ := b14e371055 X0
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e371055
                | exact resolve b14e371055 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e371055
              have b14e371207 : ∀ X0 : G, (M.op x y) = (τ (σ y)) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e16 (M.op x y)
                   have i₂ := b14e371062 X0
                   grind)
                | exact superpose b14e371062 b14e16
                | (have j1 := b14e371062 X0
                   grind)
                | exact resolve b14e16 b14e371062
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e371062
              have b14e371229 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e371207 X0
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e371207
                | (have j0 := b14e371207 x
                   grind)
                | exact resolve b14e371207 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e371207
              have b14e371236 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have j0 := b14e371229 X0
                   grind)
                | (have r₁ := b14e371229 X0
                   have r₂ := b14e28
                   grind)
                | (have r₁ := b14e371229 x
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e371229 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e371229
              have b14e371281 : y ≠ y := by
                first
                | (have i₁ := b14e28
                   have i₂ := b14e371236 x
                   grind)
                | exact superpose b14e371236 b14e28
                | (have r₁ := b14e28
                   have r₂ := b14e371236 x
                   grind)
                | exact resolve b14e28 b14e371236
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e371236
              have b14e371408 : False := by grind
              exact b14e371408
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : y ≠ (M.op x x) := by grind
            have b15e23 : x = (M.op y x) := by grind
            have b15e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e31 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b15e14 x y X0
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e32 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b15e14 y y x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e14
              | exact resolve b15e14 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e14 X2 (M.op (M.op X1 X0) X1) X3
                 have i₂ := b15e14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e35 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (k (M.op (M.op X1 X0) X1) (M.op X0 X1)) := by
              intro X0 X1
              grind
            have b15e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b15e34 X0 X1 x X3
                 have i₂ := b15e14 X0 X1 x
                 grind)
              | exact superpose b15e14 b15e34
              | exact resolve b15e34 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e34
            have b15e37 : x = (M.op x y) := by
              first
              | (have i₁ := b15e31 x
                 have i₂ := b15e32 x
                 grind)
              | exact superpose b15e32 b15e31
              | exact resolve b15e31 b15e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e31 b15e32
            have b15e38 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b15e14 y x X0
                 have i₂ := b15e37
                 grind)
              | exact superpose b15e37 b15e14
              | exact resolve b15e14 b15e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e37
            have b15e39 : (M.op x x) = (M.op y x) := by
              first
              | (have i₁ := b15e38 x
                 have i₂ := b15e36 x x x
                 grind)
              | exact superpose b15e36 b15e38
              | exact resolve b15e38 b15e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e38
            have b15e40 : x = (M.op x x) := by
              first
              | (have i₁ := b15e39
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e39
              | exact resolve b15e39 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e39
            have b15e41 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
            have b15e45 : y = (M.op x x) ∨ y = (k x y) := by grind
            clear b15e41
            have b15e47 : y = (k x y) := by
              first
              | (have r₁ := b15e45
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e45 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e45
            have b15e60 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b15e24
                 have i₂ := b15e19 (σ x) X0
                 grind)
              | (have i₁ := b15e24
                 have i₂ := b15e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b15e19 b15e24
              | (have j1 := b15e19 (σ x) X0
                 grind)
              | (have r₁ := b15e24
                 have r₂ := b15e19 (σ x) (σ y)
                 grind)
              | exact resolve b15e24 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e64 : x ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e40
                 grind)
              | exact superpose b15e40 b15e22
              | exact resolve b15e22 b15e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e40
            have b15e482 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b15e60 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e60
            have b15e483 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b15e482
                 have r₂ := b15e25
                 grind)
              | exact resolve b15e482 b15e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e482
            have b15e484 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b15e483
                 have i₂ := b15e20 x y
                 grind)
              | exact superpose b15e20 b15e483
              | exact resolve b15e483 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e483
            have b15e485 : (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b15e484
                 have i₂ := b15e47
                 grind)
              | exact superpose b15e47 b15e484
              | exact resolve b15e484 b15e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e47 b15e484
            have b15e486 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e485
                 grind)
              | exact superpose b15e485 b15e25
              | exact resolve b15e25 b15e485
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e492 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
              first
              | (have i₁ := b15e35 (σ x) (σ y)
                 have i₂ := b15e485
                 grind)
              | exact superpose b15e485 b15e35
              | exact resolve b15e35 b15e485
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e35
            have b15e493 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b15e36 (σ y) (σ x) x
                 have i₂ := b15e485
                 grind)
              | exact superpose b15e485 b15e36
              | exact resolve b15e36 b15e485
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e36 b15e485
            have b15e495 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
              first
              | (have i₁ := b15e492
                 have i₂ := b15e493 (σ x)
                 grind)
              | exact superpose b15e493 b15e492
              | exact resolve b15e492 b15e493
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e492
            have b15e501 : (σ y) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b15e495
                 have i₂ := b15e493 (σ y)
                 grind)
              | exact superpose b15e493 b15e495
              | exact resolve b15e495 b15e493
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e493 b15e495
            have b15e505 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b15e501
                 have i₂ := b15e20 y y
                 grind)
              | exact superpose b15e20 b15e501
              | exact resolve b15e501 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e501
            have b15e800 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b15e505
                 have i₂ := b15e19 y y
                 grind)
              | exact superpose b15e19 b15e505
              | (have j1 := b15e19 y y
                 grind)
              | exact resolve b15e505 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e505
            have b15e808 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
            clear b15e800
            have b15e814 : (σ x) = (σ y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b15e808
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e808
              | exact resolve b15e808 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e808
            have b15e819 : y = (M.op y y) := by
              first
              | (have r₁ := b15e814
                 have r₂ := b15e486
                 grind)
              | exact resolve b15e814 b15e486
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e486 b15e814
            have b15e823 : x = y := by
              first
              | (have i₁ := b15e819
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e819
              | exact resolve b15e819 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e819
            have b15e827 : False := by grind
            exact b15e827
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b16e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b16e23 : y ≠ (M.op x x) := by grind
              have b16e24 : x = (M.op y x) := by grind
              have b16e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b16e26 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b16e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e30 : (σ y) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b16e22
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e22
                | exact resolve b16e22 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b16e15 X2 (M.op (M.op X1 X0) X1) X3
                   have i₂ := b16e15 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b16e36 X0 X1 x X3
                   have i₂ := b16e15 X0 X1 x
                   grind)
                | exact superpose b16e15 b16e36
                | exact resolve b16e36 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e36
              have b16e46 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
                first
                | (have i₁ := b16e19 x y
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e19
                | (have j0 := b16e19 x y
                   grind)
                | (have r₁ := b16e19 x y
                   have r₂ := b16e24
                   grind)
                | exact resolve b16e19 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e52 : y = (M.op x x) ∨ y = (k x y) := by grind
              clear b16e46
              have b16e56 : y = (k x y) := by
                first
                | (have r₁ := b16e52
                   have r₂ := b16e23
                   grind)
                | exact resolve b16e52 b16e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e52
              have b16e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b16e25
                   have i₂ := b16e20 (σ x) X0
                   grind)
                | (have i₁ := b16e25
                   have i₂ := b16e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b16e20 b16e25
                | (have j1 := b16e20 (σ x) X0
                   grind)
                | (have r₁ := b16e25
                   have r₂ := b16e20 (σ x) (σ y)
                   grind)
                | exact resolve b16e25 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e461 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b16e65 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e65
              have b16e462 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b16e461
                   have r₂ := b16e26
                   grind)
                | exact resolve b16e461 b16e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e461
              have b16e463 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b16e462
                   have i₂ := b16e21 x y
                   grind)
                | exact superpose b16e21 b16e462
                | exact resolve b16e462 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e462
              have b16e464 : (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b16e463
                   have i₂ := b16e56
                   grind)
                | exact superpose b16e56 b16e463
                | exact resolve b16e463 b16e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e56 b16e463
              have b16e472 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b16e38 (σ y) (σ x) x
                   have i₂ := b16e464
                   grind)
                | exact superpose b16e464 b16e38
                | exact resolve b16e38 b16e464
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e38 b16e464
              have b16e644 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b16e30
                   have i₂ := b16e472 (σ x)
                   grind)
                | exact superpose b16e472 b16e30
                | (have r₁ := b16e30
                   have r₂ := b16e472 (σ x)
                   grind)
                | exact resolve b16e30 b16e472
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e30 b16e472
              have b16e665 : False := by grind
              exact b16e665
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : y ≠ (M.op x x) := by grind
              have b17e24 : x = (M.op y x) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b17e26 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b17e28 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 X2 (M.op (M.op X1 X0) X1) X3
                   have i₂ := b17e15 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e35 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (k (M.op (M.op X1 X0) X1) (M.op X0 X1)) := by
                intro X0 X1
                grind
              have b17e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b17e34 X0 X1 x X3
                   have i₂ := b17e15 X0 X1 x
                   grind)
                | exact superpose b17e15 b17e34
                | exact resolve b17e34 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e34
              have b17e41 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
                first
                | (have i₁ := b17e19 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e19
                | (have j0 := b17e19 x y
                   grind)
                | (have r₁ := b17e19 x y
                   have r₂ := b17e24
                   grind)
                | exact resolve b17e19 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e45 : y = (M.op x x) ∨ y = (k x y) := by grind
              clear b17e41
              have b17e48 : y = (k x y) := by
                first
                | (have r₁ := b17e45
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e45 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e45
              have b17e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b17e25
                   have i₂ := b17e20 (σ x) X0
                   grind)
                | (have i₁ := b17e25
                   have i₂ := b17e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b17e20 b17e25
                | (have j1 := b17e20 (σ x) X0
                   grind)
                | (have r₁ := b17e25
                   have r₂ := b17e20 (σ x) (σ y)
                   grind)
                | exact resolve b17e25 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e382 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b17e61 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e61
              have b17e383 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e382
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e382 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e382
              have b17e384 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e383
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e383
                | exact resolve b17e383 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e383
              have b17e385 : (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b17e384
                   have i₂ := b17e48
                   grind)
                | exact superpose b17e48 b17e384
                | exact resolve b17e384 b17e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e48 b17e384
              have b17e392 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
                first
                | (have i₁ := b17e35 (σ x) (σ y)
                   have i₂ := b17e385
                   grind)
                | exact superpose b17e385 b17e35
                | exact resolve b17e35 b17e385
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e35
              have b17e393 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b17e36 (σ y) (σ x) x
                   have i₂ := b17e385
                   grind)
                | exact superpose b17e385 b17e36
                | exact resolve b17e36 b17e385
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e385
              have b17e395 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
                first
                | (have i₁ := b17e392
                   have i₂ := b17e393 (σ x)
                   grind)
                | exact superpose b17e393 b17e392
                | exact resolve b17e392 b17e393
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e392
              have b17e401 : (σ y) = (k (σ y) (σ y)) := by
                first
                | (have i₁ := b17e395
                   have i₂ := b17e393 (σ y)
                   grind)
                | exact superpose b17e393 b17e395
                | exact resolve b17e395 b17e393
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e393 b17e395
              have b17e405 : (σ y) = (σ (k y y)) := by
                first
                | (have i₁ := b17e401
                   have i₂ := b17e21 y y
                   grind)
                | exact superpose b17e21 b17e401
                | exact resolve b17e401 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e401
              have b17e649 : (k y y) = (τ (σ y)) := by
                first
                | (have i₁ := b17e16 (k y y)
                   have i₂ := b17e405
                   grind)
                | exact superpose b17e405 b17e16
                | exact resolve b17e16 b17e405
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e405
              have b17e661 : y = (k y y) := by
                first
                | (have i₁ := b17e649
                   have i₂ := b17e16 y
                   grind)
                | exact superpose b17e16 b17e649
                | exact resolve b17e649 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e649
              have b17e706 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b17e20 y y
                   have i₂ := b17e661
                   grind)
                | exact superpose b17e661 b17e20
                | (have j0 := b17e20 y y
                   grind)
                | exact resolve b17e20 b17e661
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e661
              have b17e707 : y = (M.op y y) := by grind
              clear b17e706
              have b17e751 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b17e36 y y x
                   have i₂ := b17e707
                   grind)
                | exact superpose b17e707 b17e36
                | exact resolve b17e36 b17e707
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e36 b17e707
              have b17e784 : y ≠ y := by
                first
                | (have i₁ := b17e28
                   have i₂ := b17e751 x
                   grind)
                | exact superpose b17e751 b17e28
                | (have r₁ := b17e28
                   have r₂ := b17e751 x
                   grind)
                | exact resolve b17e28 b17e751
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e751
              have b17e803 : False := by grind
              exact b17e803
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b18e22 : x ≠ (M.op y x) := by grind
          have b18e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e43 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b18e13 y y x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e50 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X0 (M.op x y) X1
               have i₂ := b18e43 (M.op (M.op x y) X0)
               grind)
            | exact superpose b18e43 b18e13
            | exact resolve b18e13 b18e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e53 : ∀ X1 : G, x = (M.op X1 x) := by
            intro X1
            first
            | (have i₁ := b18e50 x X1
               have i₂ := b18e43 x
               grind)
            | exact superpose b18e43 b18e50
            | exact resolve b18e50 b18e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e43 b18e50
          have b18e61 : x ≠ x := by
            first
            | (have i₁ := b18e22
               have i₂ := b18e53 y
               grind)
            | exact superpose b18e53 b18e22
            | (have r₁ := b18e22
               have r₂ := b18e53 y
               grind)
            | exact resolve b18e22 b18e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e53
          have b18e67 : False := by grind
          exact b18e67
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op x x) := by grind
            have b19e23 : x ≠ (M.op y x) := by grind
            have b19e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e29 : (σ x) = (k (σ x) (σ y)) := by grind
            have b19e30 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b19e29
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e29
              | exact resolve b19e29 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e29
            have b19e31 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e30
                 grind)
              | exact superpose b19e30 b19e15
              | exact resolve b19e15 b19e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30
            have b19e32 : x = (k x y) := by
              first
              | (have i₁ := b19e31
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e31
              | exact resolve b19e31 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e31
            have b19e73 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b19e32
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e32
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e32 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e32
            have b19e82 : x = (M.op y x) ∨ y = (M.op x x) := by grind
            clear b19e73
            have b19e86 : y = (M.op x x) := by
              first
              | (have r₁ := b19e82
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e82 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e82
            have b19e89 : False := by grind
            exact b19e89
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op x x) := by grind
            have b20e23 : x ≠ (M.op y x) := by grind
            have b20e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : (σ x) = (k (σ x) (σ y)) := by grind
            have b20e29 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b20e28
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e28
              | exact resolve b20e28 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e30 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e29
                 grind)
              | exact superpose b20e29 b20e15
              | exact resolve b20e15 b20e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e31 : x = (k x y) := by
              first
              | (have i₁ := b20e30
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e30
              | exact resolve b20e30 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e85 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b20e31
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e31
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e31 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31
            have b20e95 : x = (M.op y x) ∨ y = (M.op x x) := by grind
            clear b20e85
            have b20e99 : y = (M.op x x) := by
              first
              | (have r₁ := b20e95
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e95 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e95
            have b20e102 : False := by grind
            exact b20e102
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b21e23 : x ≠ (M.op y x) := by grind
            have b21e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e31 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b21e14 y y x
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e38 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X0 (M.op x y) X1
                 have i₂ := b21e31 (M.op (M.op x y) X0)
                 grind)
              | exact superpose b21e31 b21e14
              | exact resolve b21e14 b21e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e41 : ∀ X1 : G, x = (M.op X1 x) := by
              intro X1
              first
              | (have i₁ := b21e38 x X1
                 have i₂ := b21e31 x
                 grind)
              | exact superpose b21e31 b21e38
              | exact resolve b21e38 b21e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e31 b21e38
            have b21e52 : x ≠ x := by
              first
              | (have i₁ := b21e23
                 have i₂ := b21e41 y
                 grind)
              | exact superpose b21e41 b21e23
              | (have r₁ := b21e23
                 have r₂ := b21e41 y
                 grind)
              | exact resolve b21e23 b21e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e41
            have b21e58 : False := by grind
            exact b21e58
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e24 : x ≠ (M.op y x) := by grind
              have b22e26 : (σ x) = (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b22e15 X2 (M.op (M.op X1 X0) X1) X3
                   have i₂ := b22e15 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e37 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (k (M.op (M.op X1 X0) X1) (M.op X0 X1)) := by
                intro X0 X1
                grind
              have b22e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b22e36 X0 X1 x X3
                   have i₂ := b22e15 X0 X1 x
                   grind)
                | exact superpose b22e15 b22e36
                | exact resolve b22e36 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e36
              have b22e79 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b22e38 (σ y) (σ x) x
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e38
                | exact resolve b22e38 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e317 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
                first
                | (have i₁ := b22e37 (σ y) (σ x)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e37
                | exact resolve b22e37 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e37
              have b22e322 : (σ x) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b22e317
                   have i₂ := b22e79 (M.op (σ x) (σ y))
                   grind)
                | exact superpose b22e79 b22e317
                | exact resolve b22e317 b22e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e79 b22e317
              have b22e342 : (σ x) = (σ (k x x)) := by
                first
                | (have i₁ := b22e322
                   have i₂ := b22e21 x x
                   grind)
                | exact superpose b22e21 b22e322
                | exact resolve b22e322 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e322
              have b22e437 : (k x x) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (k x x)
                   have i₂ := b22e342
                   grind)
                | exact superpose b22e342 b22e16
                | exact resolve b22e16 b22e342
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e342
              have b22e440 : x = (k x x) := by
                first
                | (have i₁ := b22e437
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e437
                | exact resolve b22e437 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e437
              have b22e510 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b22e20 x x
                   have i₂ := b22e440
                   grind)
                | exact superpose b22e440 b22e20
                | (have j0 := b22e20 x x
                   grind)
                | exact resolve b22e20 b22e440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e440
              have b22e511 : x = (M.op x x) := by grind
              clear b22e510
              have b22e626 : ∀ X0 : G, x = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b22e38 x x x
                   have i₂ := b22e511
                   grind)
                | exact superpose b22e511 b22e38
                | exact resolve b22e38 b22e511
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e38 b22e511
              have b22e697 : x ≠ x := by
                first
                | (have i₁ := b22e24
                   have i₂ := b22e626 y
                   grind)
                | exact superpose b22e626 b22e24
                | (have r₁ := b22e24
                   have r₂ := b22e626 y
                   grind)
                | exact resolve b22e24 b22e626
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e626
              have b22e715 : False := by grind
              exact b22e715
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : y ≠ (M.op x x) := by grind
              have b23e24 : x ≠ (M.op y x) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b23e26 : (σ x) = (M.op (σ y) (σ x)) := by grind
              have b23e28 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X2 (M.op (M.op X1 X0) X1) X3
                   have i₂ := b23e15 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b23e34 X0 X1 x X3
                   have i₂ := b23e15 X0 X1 x
                   grind)
                | exact superpose b23e15 b23e34
                | exact resolve b23e34 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e34
              have b23e46 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
              have b23e50 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
              clear b23e46
              have b23e53 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e50
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e50 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e50
              have b23e55 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b23e53
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e53
                | exact resolve b23e53 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e53
              have b23e59 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e55
                   grind)
                | exact superpose b23e55 b23e16
                | exact resolve b23e16 b23e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e55
              have b23e60 : y = (k x y) := by
                first
                | (have i₁ := b23e59
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e59
                | exact resolve b23e59 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e59
              have b23e80 : y = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e60
                   grind)
                | exact superpose b23e60 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e60
              have b23e81 : y = (M.op y x) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b23e80
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e80 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e80
              have b23e83 : y = (M.op y x) := by
                first
                | (have r₁ := b23e81
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e81 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e81
              have b23e94 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b23e36 y x x
                   have i₂ := b23e83
                   grind)
                | exact superpose b23e83 b23e36
                | exact resolve b23e36 b23e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e36 b23e83
              have b23e118 : y ≠ y := by
                first
                | (have i₁ := b23e28
                   have i₂ := b23e94 x
                   grind)
                | exact superpose b23e94 b23e28
                | (have r₁ := b23e28
                   have r₂ := b23e94 x
                   grind)
                | exact resolve b23e28 b23e94
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e94
              have b23e125 : False := by grind
              exact b23e125
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b24e23 : x ≠ (M.op y x) := by grind
            have b24e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e31 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b24e14 y y x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e37 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X0 (M.op x y) X1
                 have i₂ := b24e31 (M.op (M.op x y) X0)
                 grind)
              | exact superpose b24e31 b24e14
              | exact resolve b24e14 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e40 : ∀ X1 : G, x = (M.op X1 x) := by
              intro X1
              first
              | (have i₁ := b24e37 x X1
                 have i₂ := b24e31 x
                 grind)
              | exact superpose b24e31 b24e37
              | exact resolve b24e37 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e31 b24e37
            have b24e47 : x ≠ x := by
              first
              | (have i₁ := b24e23
                 have i₂ := b24e40 y
                 grind)
              | exact superpose b24e40 b24e23
              | (have r₁ := b24e23
                 have r₂ := b24e40 y
                 grind)
              | exact resolve b24e23 b24e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e40
            have b24e53 : False := by grind
            exact b24e53
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b25e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b25e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e30 : (σ y) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e22
                | exact resolve b25e22 b25e28
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
              have b25e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 X2 (M.op (M.op X1 X0) X1) X3
                   have i₂ := b25e15 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b25e35 X0 X1 x X3
                   have i₂ := b25e15 X0 X1 x
                   grind)
                | exact superpose b25e15 b25e35
                | exact resolve b25e35 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35
              have b25e64 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b25e37 x y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e37
                | exact resolve b25e37 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e91 : ∀ X0 : G, y ≠ y ∨ (M.op y y) = X0 ∨ (k y X0) = X0 := by
                intro X0
                first
                | (have i₁ := b25e19 y X0
                   have i₂ := b25e64 X0
                   grind)
                | exact superpose b25e64 b25e19
                | (have j0 := b25e19 y X0
                   grind)
                | (have r₁ := b25e19 y X0
                   have r₂ := b25e64 X0
                   grind)
                | exact resolve b25e19 b25e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e93 : ∀ X0 : G, (M.op y y) = X0 ∨ (k y X0) = X0 := by
                intro X0
                first
                | (have j0 := b25e91 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e91
              have b25e94 : ∀ X0 : G, (k y X0) = X0 ∨ y = X0 := by
                intro X0
                first
                | (have i₁ := b25e93 X0
                   have i₂ := b25e64 y
                   grind)
                | exact superpose b25e64 b25e93
                | (have j0 := b25e93 X0
                   grind)
                | exact resolve b25e93 b25e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e64 b25e93
              have b25e102 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e16 (k X0 (τ X1))
                   have i₂ := b25e32 X1 X0
                   grind)
                | exact superpose b25e32 b25e16
                | exact resolve b25e16 b25e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e32
              have b25e698 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
                intro X0
                grind
              clear b25e102
              have b25e715 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e698 X0
                   have i₂ := b25e16 X0
                   grind)
                | exact superpose b25e16 b25e698
                | exact resolve b25e698 b25e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e698
              have b25e923 : y = (τ (M.op (σ y) (σ y))) ∨ y = (τ (M.op (σ y) (σ y))) := by
                first
                | (have i₁ := b25e94 (τ (M.op (σ y) (σ y)))
                   have i₂ := b25e715 y
                   grind)
                | exact superpose b25e715 b25e94
                | (have j0 := b25e94 (τ (M.op (σ y) (σ y)))
                   grind)
                | exact resolve b25e94 b25e715
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e94 b25e715
              have b25e924 : y = (τ (M.op (σ y) (σ y))) := by grind
              clear b25e923
              have b25e1005 : (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b25e17 (M.op (σ y) (σ y))
                   have i₂ := b25e924
                   grind)
                | exact superpose b25e924 b25e17
                | exact resolve b25e17 b25e924
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e924
              have b25e1082 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b25e37 (σ y) (σ y) x
                   have i₂ := b25e1005
                   grind)
                | exact superpose b25e1005 b25e37
                | exact resolve b25e37 b25e1005
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e37 b25e1005
              have b25e1158 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b25e30
                   have i₂ := b25e1082 (σ x)
                   grind)
                | exact superpose b25e1082 b25e30
                | (have r₁ := b25e30
                   have r₂ := b25e1082 (σ x)
                   grind)
                | exact resolve b25e30 b25e1082
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e30 b25e1082
              have b25e1183 : False := by grind
              exact b25e1183
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e24 : x ≠ (M.op y x) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b26e28 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
              have b26e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X2 (M.op (M.op X1 X0) X1) X3
                   have i₂ := b26e15 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e35 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e33 X0 X1 x X3
                   have i₂ := b26e15 X0 X1 x
                   grind)
                | exact superpose b26e15 b26e33
                | exact resolve b26e33 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e33
              have b26e45 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e19 (M.op X0 X1) X2
                   have i₂ := b26e35 X0 X1 X2
                   grind)
                | exact superpose b26e35 b26e19
                | (have j0 := b26e19 (M.op X0 X1) X2
                   grind)
                | (have r₁ := b26e19 (M.op X0 X1) x
                   have r₂ := b26e35 X0 X1 x
                   grind)
                | exact resolve b26e19 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e46 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e45 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e45
              have b26e47 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 ∨ (M.op X0 X1) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e46 X0 X1 X2
                   have i₂ := b26e35 X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b26e35 b26e46
                | (have j0 := b26e46 X0 X1 X2
                   grind)
                | exact resolve b26e46 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e46
              have b26e68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
              have b26e69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e72 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 X0 X0 x
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e35 X0 X1 x
                   have i₂ := b26e20 X0 (M.op X0 X1)
                   grind)
                | exact superpose b26e20 b26e35
                | (have j1 := b26e20 X1 X0
                   grind)
                | exact resolve b26e35 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e79 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
                intro X0
                grind
              clear b26e30
              have b26e84 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e79 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e79
                | exact resolve b26e79 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e79
              have b26e297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e69 (σ X1) (σ X0)
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e69
                | (have j0 := b26e69 (σ X1) (σ X0)
                   grind)
                | exact resolve b26e69 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e69
              have b26e398 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op X2 (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 (σ X1) (σ X1) x
                   have i₂ := b26e68 X0 X1
                   grind)
                | exact superpose b26e68 b26e35
                | (have j1 := b26e68 X0 X1
                   grind)
                | exact resolve b26e35 b26e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68
              have b26e568 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e84 (M.op X0 X1)
                   have i₂ := b26e47 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   grind)
                | exact superpose b26e47 b26e84
                | (have j1 := b26e47 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   grind)
                | exact resolve b26e84 b26e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e47 b26e84
              have b26e572 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have j0 := b26e568 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e568
              have b26e1007 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X0 X3) = (k X3 X0) ∨ (M.op X0 X3) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X1 X0 X2
                   have i₂ := b26e72 X0 X3 (M.op X0 X1)
                   grind)
                | exact superpose b26e72 b26e15
                | (have j1 := b26e72 X0 X3 X2
                   grind)
                | exact resolve b26e15 b26e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e2077 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))
                   have i₂ := b26e572 X0 X1
                   grind)
                | exact superpose b26e572 b26e16
                | exact resolve b26e16 b26e572
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e572
              have b26e2323 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e297 y x
                   grind)
                | exact superpose b26e297 b26e22
                | (have j1 := b26e297 y x
                   grind)
                | exact resolve b26e22 b26e297
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e297
              have b26e2543 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e26
                   have i₂ := b26e398 x X0 (σ y)
                   grind)
                | exact superpose b26e398 b26e26
                | (have j1 := b26e398 x X0 x
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e398 x x (σ y)
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e398 y x x
                   grind)
                | exact resolve b26e26 b26e398
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e398
              have b26e2572 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e2543 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2543
              have b26e4334 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
                   have i₂ := b26e2077 X0 X1
                   grind)
                | exact superpose b26e2077 b26e35
                | exact resolve b26e35 b26e2077
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e35 b26e2077
              have b26e16340 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e2572 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2572
              have b26e17621 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e24
                   have i₂ := b26e1007 x y X0 X1
                   grind)
                | (have i₁ := b26e24
                   have i₂ := b26e1007 x X0 y X1
                   grind)
                | exact superpose b26e1007 b26e24
                | (have j1 := b26e1007 x X1 x X1
                   grind)
                | (have r₁ := b26e24
                   have r₂ := b26e1007 y X1 x x
                   grind)
                | exact resolve b26e24 b26e1007
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1007
              have b26e17802 : ∀ X1 : G, (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X1
                first
                | (have j0 := b26e17621 x X1
                   have j1 := b26e72 x X1 x
                   grind)
                | (have r₁ := b26e17621 x X1
                   have r₂ := b26e72 x X1 x
                   grind)
                | (have r₁ := b26e17621 x X1
                   have r₂ := b26e72 x x x
                   grind)
                | exact resolve b26e17621 b26e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72 b26e17621
              have b26e23600 : ∀ X0 : G, (σ X0) ≠ (σ (M.op x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (M.op x X0) = X0 := by
                intro X0
                first
                | (have i₁ := b26e16340 X0
                   have i₂ := b26e17802 X0
                   grind)
                | exact superpose b26e17802 b26e16340
                | (have j0 := b26e16340 X0
                   have j1 := b26e17802 X0
                   grind)
                | exact resolve b26e16340 b26e17802
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e16340
              have b26e58134 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b26e2323
                   have i₂ := b26e17802 y
                   grind)
                | exact superpose b26e17802 b26e2323
                | (have j1 := b26e17802 y
                   grind)
                | exact resolve b26e2323 b26e17802
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2323 b26e17802
              have b26e58164 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
              clear b26e58134
              have b26e58180 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
                first
                | (have j1 := b26e23600 y
                   grind)
                | (have r₁ := b26e58164
                   have r₂ := b26e23600 y
                   grind)
                | exact resolve b26e58164 b26e23600
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e23600 b26e58164
              have b26e58193 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e58180
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e58180 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e58180
              have b26e58243 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) := by
                intro X0
                first
                | (have i₁ := b26e4334 (σ x) (σ y) x
                   have i₂ := b26e58193
                   grind)
                | exact superpose b26e58193 b26e4334
                | exact resolve b26e4334 b26e58193
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4334 b26e58193
              have b26e58272 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b26e58243 X0
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e58243
                | exact resolve b26e58243 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e58243
              have b26e58350 : y ≠ y := by
                first
                | (have i₁ := b26e28
                   have i₂ := b26e58272 x
                   grind)
                | exact superpose b26e58272 b26e28
                | (have r₁ := b26e28
                   have r₂ := b26e58272 x
                   grind)
                | exact resolve b26e28 b26e58272
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e58272
              have b26e58425 : False := by grind
              exact b26e58425

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyy_x_pyx_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
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
        have b0e30 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b0e12 x y X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e12 X2 (M.op (M.op X1 X0) X1) X3
             have i₂ := b0e12 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e32 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b0e31 X0 X1 x X3
             have i₂ := b0e12 X0 X1 x
             grind)
          | exact superpose b0e12 b0e31
          | exact resolve b0e31 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e31
        have b0e33 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e30 X0
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e30
          | exact resolve b0e30 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e30
        have b0e39 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b0e15 y X0
             have i₂ := b0e33 X0
             grind)
          | exact superpose b0e33 b0e15
          | (have j0 := b0e15 y X0
             grind)
          | (have r₁ := b0e15 y X0
             have r₂ := b0e33 X0
             grind)
          | exact resolve b0e15 b0e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e40 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e15 (σ x) (σ y)
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e15
          | (have j0 := b0e15 (σ x) (σ y)
             grind)
          | (have r₁ := b0e15 (σ x) (σ y)
             have r₂ := b0e21
             grind)
          | exact resolve b0e15 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e42 : x ≠ x ∨ (k x y) = (M.op y y) := by
          first
          | (have i₁ := b0e15 x y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e15
          | (have j0 := b0e15 x y
             grind)
          | (have r₁ := b0e15 x y
             have r₂ := b0e20
             grind)
          | exact resolve b0e15 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e43 : (k x y) = (M.op y y) := by grind
        clear b0e42
        have b0e45 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b0e40
        have b0e46 : ∀ X0 : G, (M.op X0 X0) = (k y X0) := by
          intro X0
          first
          | (have j0 := b0e39 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39
        have b0e47 : y = (k x y) := by
          first
          | (have i₁ := b0e43
             have i₂ := b0e33 y
             grind)
          | exact superpose b0e33 b0e43
          | exact resolve b0e43 b0e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e33 b0e43
        have b0e49 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b0e45
             have i₂ := b0e18 x y
             grind)
          | exact superpose b0e18 b0e45
          | exact resolve b0e45 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e45
        have b0e51 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e49
             have i₂ := b0e47
             grind)
          | exact superpose b0e47 b0e49
          | exact resolve b0e49 b0e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e47 b0e49
        have b0e52 : (σ y) = (k y (σ y)) := by
          first
          | (have i₁ := b0e51
             have i₂ := b0e46 (σ y)
             grind)
          | exact superpose b0e46 b0e51
          | exact resolve b0e51 b0e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e51
        have b0e101 : ∀ X0 X1 : G, (k y X0) = (M.op X1 (k y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e32 X0 X0 x
             have i₂ := b0e46 X0
             grind)
          | exact superpose b0e46 b0e32
          | exact resolve b0e32 b0e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e32 b0e46
        have b0e853 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e101 (σ y) x
             have i₂ := b0e52
             grind)
          | exact superpose b0e52 b0e101
          | exact resolve b0e101 b0e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e52 b0e101
        have b0e1086 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b0e24
             have i₂ := b0e853 (σ x)
             grind)
          | exact superpose b0e853 b0e24
          | (have r₁ := b0e24
             have r₂ := b0e853 (σ x)
             grind)
          | exact resolve b0e24 b0e853
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24 b0e853
        have b0e1087 : False := by grind
        exact b0e1087
      · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
          have b1e32 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b1e13 x y X0
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e13
            | exact resolve b1e13 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e33 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
          have b1e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b1e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b1e36 X0 X1 x X3
               have i₂ := b1e13 X0 X1 x
               grind)
            | exact superpose b1e13 b1e36
            | exact resolve b1e36 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e36
          have b1e38 : x = (M.op x y) := by
            first
            | (have i₁ := b1e32 x
               have i₂ := b1e33 x
               grind)
            | exact superpose b1e33 b1e32
            | exact resolve b1e32 b1e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e32 b1e33
          have b1e44 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
          have b1e46 : x ≠ x ∨ (M.op y y) = (k x y) := by
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
          have b1e48 : (M.op y y) = (k x y) := by grind
          clear b1e46
          have b1e49 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear b1e44
          have b1e50 : x = (k x y) := by
            first
            | (have i₁ := b1e48
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e48
            | exact resolve b1e48 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e48
          have b1e51 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b1e49
               have i₂ := b1e19 x y
               grind)
            | exact superpose b1e19 b1e49
            | exact resolve b1e49 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e49
          have b1e52 : (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b1e51
               have i₂ := b1e50
               grind)
            | exact superpose b1e50 b1e51
            | exact resolve b1e51 b1e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e50 b1e51
          have b1e96 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b1e13 (σ y) (σ y) x
               have i₂ := b1e52
               grind)
            | exact superpose b1e52 b1e13
            | exact resolve b1e13 b1e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e52
          have b1e100 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e96 x
               have i₂ := b1e37 (σ x) (σ y) x
               grind)
            | exact superpose b1e37 b1e96
            | exact resolve b1e96 b1e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e37 b1e96
          have b1e386 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e100
               grind)
            | exact superpose b1e100 b1e20
            | exact resolve b1e20 b1e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e100
          have b1e396 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b1e386
               have i₂ := b1e38
               grind)
            | exact superpose b1e38 b1e386
            | exact resolve b1e386 b1e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e38 b1e386
          have b1e397 : False := by grind
          exact b1e397
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : x = (M.op y x) := by grind
          have b2e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
          have b2e23 : y ≠ (M.op x y) := by grind
          have b2e24 : x ≠ (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b2e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b2e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k (τ X0) X1)
               have i₂ := b2e26 X0 X1
               grind)
            | exact superpose b2e26 b2e14
            | exact resolve b2e14 b2e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e26
          have b2e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b2e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b2e35 X0 X1 x X3
               have i₂ := b2e13 X0 X1 x
               grind)
            | exact superpose b2e13 b2e35
            | exact resolve b2e35 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e35
          have b2e40 : x ≠ x ∨ (M.op y y) = (k x y) := by
            first
            | (have i₁ := b2e16 x y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e16
            | (have j0 := b2e16 x y
               grind)
            | (have r₁ := b2e16 x y
               have r₂ := b2e21
               grind)
            | exact resolve b2e16 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e46 : (M.op y y) = (k x y) := by grind
          clear b2e40
          have b2e53 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b2e36 y x x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e36
            | exact resolve b2e36 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e54 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b2e36 (σ y) (σ x) x
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e36
            | exact resolve b2e36 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 X0
               have i₂ := b2e18 (σ X1) (σ X0)
               grind)
            | exact superpose b2e18 b2e19
            | (have j1 := b2e18 (σ X1) (σ X0)
               grind)
            | exact resolve b2e19 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e86 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b2e16 x X0
               have i₂ := b2e53 X0
               grind)
            | exact superpose b2e53 b2e16
            | (have j0 := b2e16 x X0
               grind)
            | (have r₁ := b2e16 x X0
               have r₂ := b2e53 X0
               grind)
            | exact resolve b2e16 b2e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e53
          have b2e89 : ∀ X0 : G, (M.op X0 X0) = (k x X0) := by
            intro X0
            first
            | (have j0 := b2e86 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e86
          have b2e97 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k X0 (τ X1))
               have i₂ := b2e27 X1 X0
               grind)
            | exact superpose b2e27 b2e14
            | exact resolve b2e14 b2e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e27
          have b2e104 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b2e16 (σ x) X0
               have i₂ := b2e54 X0
               grind)
            | exact superpose b2e54 b2e16
            | (have j0 := b2e16 (σ x) X0
               grind)
            | (have r₁ := b2e16 (σ x) X0
               have r₂ := b2e54 X0
               grind)
            | exact resolve b2e16 b2e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e54
          have b2e107 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b2e104 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e104
          have b2e128 : ∀ X0 X1 : G, (k x X0) = (M.op X1 (k x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e36 X0 X0 x
               have i₂ := b2e89 X0
               grind)
            | exact superpose b2e89 b2e36
            | exact resolve b2e36 b2e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e324 : ∀ X0 : G, (k x X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b2e89 X0
               have i₂ := b2e107 X0
               grind)
            | exact superpose b2e107 b2e89
            | exact resolve b2e89 b2e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e691 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 X1
               have i₂ := b2e72 X1 X0
               grind)
            | exact superpose b2e72 b2e14
            | (have j1 := b2e72 X1 X0
               grind)
            | exact resolve b2e14 b2e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e72
          have b2e748 : ∀ X0 X1 : G, (τ (k x (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e691 X0 X1
               have i₂ := b2e89 (σ X0)
               grind)
            | exact superpose b2e89 b2e691
            | (have j0 := b2e691 X0 X1
               grind)
            | exact resolve b2e691 b2e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e89 b2e691
          have b2e797 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k (τ x) X0) = X1 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e748 X0 X1
               have i₂ := b2e31 x X0
               grind)
            | exact superpose b2e31 b2e748
            | (have j0 := b2e748 X0 X1
               grind)
            | exact resolve b2e748 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e748
          have b2e944 : ∀ X0 : G, (τ (k x (σ X0))) = (k (τ (σ x)) X0) := by
            intro X0
            first
            | (have i₁ := b2e31 (σ x) X0
               have i₂ := b2e324 (σ X0)
               grind)
            | exact superpose b2e324 b2e31
            | exact resolve b2e31 b2e324
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e324
          have b2e952 : ∀ X0 : G, (k x X0) = (τ (k x (σ X0))) := by
            intro X0
            first
            | (have i₁ := b2e944 X0
               have i₂ := b2e14 x
               grind)
            | exact superpose b2e14 b2e944
            | exact resolve b2e944 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e944
          have b2e959 : ∀ X0 : G, (k x X0) = (k (τ x) X0) := by
            intro X0
            first
            | (have i₁ := b2e952 X0
               have i₂ := b2e31 x X0
               grind)
            | exact superpose b2e31 b2e952
            | exact resolve b2e952 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e31 b2e952
          have b2e985 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b2e97 x X0
               have i₂ := b2e107 X0
               grind)
            | exact superpose b2e107 b2e97
            | exact resolve b2e97 b2e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e97 b2e107
          have b2e3031 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (k x (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e985 (M.op X0 X1)
               have i₂ := b2e36 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b2e36 b2e985
            | exact resolve b2e985 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36 b2e985
          have b2e5168 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k (τ x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e797 y x
               grind)
            | exact superpose b2e797 b2e20
            | (have j1 := b2e797 y x
               grind)
            | exact resolve b2e20 b2e797
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e797
          have b2e5222 : x = (k x y) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b2e5168
               have i₂ := b2e959 y
               grind)
            | exact superpose b2e959 b2e5168
            | exact resolve b2e5168 b2e959
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e959 b2e5168
          have b2e5275 : x = (M.op y y) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b2e5222
               have i₂ := b2e46
               grind)
            | exact superpose b2e46 b2e5222
            | exact resolve b2e5222 b2e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e46 b2e5222
          have b2e5310 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b2e5275
               have r₂ := b2e24
               grind)
            | exact resolve b2e5275 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e5275
          have b2e22745 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e128 (τ (M.op X0 X1)) X1
               have i₂ := b2e3031 X0 X1
               grind)
            | exact superpose b2e3031 b2e128
            | exact resolve b2e128 b2e3031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e128 b2e3031
          have b2e33982 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e5310
               have i₂ := b2e18 y x
               grind)
            | exact superpose b2e18 b2e5310
            | (have j1 := b2e18 y x
               grind)
            | exact resolve b2e5310 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e5310
          have b2e33995 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
          clear b2e33982
          have b2e34000 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b2e33995
               have r₂ := b2e24
               grind)
            | exact resolve b2e33995 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e33995
          have b2e34001 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b2e34000
               have r₂ := b2e23
               grind)
            | exact resolve b2e34000 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e34000
          have b2e34042 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b2e22745 (σ x) (σ y) x
               have i₂ := b2e34001
               grind)
            | exact superpose b2e34001 b2e22745
            | exact resolve b2e22745 b2e34001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e22745 b2e34001
          have b2e34052 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e34042 X0
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e34042
            | exact resolve b2e34042 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e34042
          have b2e34739 : y ≠ y := by
            first
            | (have i₁ := b2e23
               have i₂ := b2e34052 x
               grind)
            | exact superpose b2e34052 b2e23
            | (have r₁ := b2e23
               have r₂ := b2e34052 x
               grind)
            | exact resolve b2e23 b2e34052
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e34052
          have b2e34758 : False := by grind
          exact b2e34758
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : x = (M.op y x) := by grind
          have b3e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b3e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b3e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e36 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b3e13 x y X0
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e13
            | exact resolve b3e13 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e39 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b3e36 X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e36
            | exact resolve b3e36 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e36
          have b3e48 : x ≠ x ∨ (k x y) = (M.op y y) := by
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
          have b3e49 : (k x y) = (M.op y y) := by grind
          clear b3e48
          have b3e52 : y = (k x y) := by
            first
            | (have i₁ := b3e49
               have i₂ := b3e39 y
               grind)
            | exact superpose b3e39 b3e49
            | exact resolve b3e49 b3e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e39 b3e49
          have b3e64 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          have b3e67 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e64
               have r₂ := b3e22
               grind)
            | exact resolve b3e64 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e64
          have b3e69 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b3e67
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e67
            | exact resolve b3e67 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e67
          have b3e71 : (σ x) = (σ y) := by
            first
            | (have i₁ := b3e69
               have i₂ := b3e52
               grind)
            | exact superpose b3e52 b3e69
            | exact resolve b3e69 b3e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e52 b3e69
          have b3e95 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e71
               grind)
            | exact superpose b3e71 b3e22
            | exact resolve b3e22 b3e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e102 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e95
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e95
            | exact resolve b3e95 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e95
          have b3e104 : False := by grind
          exact b3e104
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b4e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b4e22 : x = (M.op y x) := by grind
            have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b4e25 : y ≠ (M.op x y) := by grind
            have b4e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e30 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b4e14 x y X0
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e14
              | exact resolve b4e14 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e31 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
            have b4e32 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ x))) := by
              intro X0
              first
              | (have i₁ := b4e14 (σ x) (σ x) x
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e14
              | exact resolve b4e14 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b4e14 X2 (M.op (M.op X1 X0) X1) X3
                 have i₂ := b4e14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                 grind)
              | exact superpose b4e14 b4e14
              | exact resolve b4e14 b4e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e35 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b4e34 X0 X1 x X3
                 have i₂ := b4e14 X0 X1 x
                 grind)
              | exact superpose b4e14 b4e34
              | exact resolve b4e34 b4e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e34
            have b4e36 : x = (M.op x y) := by
              first
              | (have i₁ := b4e30 x
                 have i₂ := b4e31 x
                 grind)
              | exact superpose b4e31 b4e30
              | exact resolve b4e30 b4e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e30 b4e31
            have b4e37 : x ≠ y := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e36
                 grind)
              | exact superpose b4e36 b4e25
              | exact resolve b4e25 b4e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e96 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b4e35 (σ x) (σ x) x
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e35
              | exact resolve b4e35 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e170 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b4e17 (σ y) X0
                 have i₂ := b4e96 X0
                 grind)
              | exact superpose b4e96 b4e17
              | (have j0 := b4e17 (σ y) X0
                 grind)
              | (have r₁ := b4e17 (σ y) X0
                 have r₂ := b4e96 X0
                 grind)
              | exact resolve b4e17 b4e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e173 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b4e21
                 have i₂ := b4e96 (σ x)
                 grind)
              | exact superpose b4e96 b4e21
              | exact resolve b4e21 b4e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e96
            have b4e174 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have j0 := b4e170 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e170
            have b4e175 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b4e173
                 have i₂ := b4e36
                 grind)
              | exact superpose b4e36 b4e173
              | exact resolve b4e173 b4e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e36 b4e173
            have b4e180 : (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b4e35 (σ y) (σ x) x
                 have i₂ := b4e32 x
                 grind)
              | exact superpose b4e32 b4e35
              | exact resolve b4e35 b4e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e35
            have b4e450 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) := by
              first
              | (have i₁ := b4e32 (M.op (σ y) (σ x))
                 have i₂ := b4e174 (M.op (σ y) (σ x))
                 grind)
              | exact superpose b4e174 b4e32
              | exact resolve b4e32 b4e174
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e32 b4e174
            have b4e464 : (σ y) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b4e450
                 have i₂ := b4e180
                 grind)
              | exact superpose b4e180 b4e450
              | exact resolve b4e450 b4e180
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e180 b4e450
            have b4e480 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b4e464
                 have i₂ := b4e20 y y
                 grind)
              | exact superpose b4e20 b4e464
              | exact resolve b4e464 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e464
            have b4e523 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b4e480
                 have i₂ := b4e19 y y
                 grind)
              | exact superpose b4e19 b4e480
              | (have j1 := b4e19 y y
                 grind)
              | exact resolve b4e480 b4e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e480
            have b4e527 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
            clear b4e523
            have b4e532 : (σ x) = (σ y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b4e527
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e527
              | exact resolve b4e527 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e527
            have b4e535 : y = (M.op y y) := by
              first
              | (have r₁ := b4e532
                 have r₂ := b4e175
                 grind)
              | exact resolve b4e532 b4e175
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e175 b4e532
            have b4e537 : x = y := by
              first
              | (have i₁ := b4e535
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e535
              | exact resolve b4e535 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e535
            have b4e539 : False := by grind
            exact b4e539
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
            have b5e38 : x ≠ x ∨ (M.op y y) = (k x y) := by
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
            have b5e43 : (M.op y y) = (k x y) := by grind
            clear b5e38
            have b5e45 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b5e48 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e45
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e45 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e45
            have b5e49 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b5e48
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e48
              | exact resolve b5e48 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e48
            have b5e50 : (σ x) = (σ (M.op y y)) := by
              first
              | (have i₁ := b5e49
                 have i₂ := b5e43
                 grind)
              | exact superpose b5e43 b5e49
              | exact resolve b5e49 b5e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e43 b5e49
            have b5e53 : (M.op y y) = (τ (σ x)) := by
              first
              | (have i₁ := b5e15 (M.op y y)
                 have i₂ := b5e50
                 grind)
              | exact superpose b5e50 b5e15
              | exact resolve b5e15 b5e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e50
            have b5e54 : x = (M.op y y) := by
              first
              | (have i₁ := b5e53
                 have i₂ := b5e15 x
                 grind)
              | exact superpose b5e15 b5e53
              | exact resolve b5e53 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e53
            have b5e57 : False := by grind
            exact b5e57
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e21 : x = (M.op y x) := by grind
          have b6e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b6e33 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b6e13 x y X0
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e34 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b6e13 y x X0
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b6e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e36 X0 X1 x X3
               have i₂ := b6e13 X0 X1 x
               grind)
            | exact superpose b6e13 b6e36
            | exact resolve b6e36 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e36
          have b6e38 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b6e34 X0
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e34
            | exact resolve b6e34 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e34
          have b6e39 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b6e33 X0
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e33
            | exact resolve b6e33 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e33
          have b6e46 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b6e16 x X0
               have i₂ := b6e38 X0
               grind)
            | exact superpose b6e38 b6e16
            | (have j0 := b6e16 x X0
               grind)
            | (have r₁ := b6e16 x X0
               have r₂ := b6e38 X0
               grind)
            | exact resolve b6e16 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e38
          have b6e47 : ∀ X0 : G, (M.op X0 X0) = (k x X0) := by
            intro X0
            first
            | (have j0 := b6e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e46
          have b6e75 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
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
          have b6e532 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b6e75 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e75
          have b6e533 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b6e532
               have r₂ := b6e22
               grind)
            | exact resolve b6e532 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e532
          have b6e534 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b6e533
               have i₂ := b6e19 x y
               grind)
            | exact superpose b6e19 b6e533
            | exact resolve b6e533 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e533
          have b6e535 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b6e534
               have i₂ := b6e47 y
               grind)
            | exact superpose b6e47 b6e534
            | exact resolve b6e534 b6e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e47 b6e534
          have b6e536 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b6e535
               have i₂ := b6e39 y
               grind)
            | exact superpose b6e39 b6e535
            | exact resolve b6e535 b6e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e39 b6e535
          have b6e542 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e37 (σ y) (σ x) x
               have i₂ := b6e536
               grind)
            | exact superpose b6e536 b6e37
            | exact resolve b6e37 b6e536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e37 b6e536
          have b6e685 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b6e26
               have i₂ := b6e542 (σ x)
               grind)
            | exact superpose b6e542 b6e26
            | (have r₁ := b6e26
               have r₂ := b6e542 (σ x)
               grind)
            | exact resolve b6e26 b6e542
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26 b6e542
          have b6e687 : False := by grind
          exact b6e687
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e22 : x = (M.op y x) := by grind
            have b7e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b7e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b7e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e40 : x ≠ x ∨ (M.op y y) = (k x y) := by
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
            have b7e44 : (M.op y y) = (k x y) := by grind
            clear b7e40
            have b7e45 : x = (k x y) := by
              first
              | (have i₁ := b7e44
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e44
              | exact resolve b7e44 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e44
            have b7e59 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
            have b7e594 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b7e59 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e59
            have b7e595 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b7e594
                 have r₂ := b7e23
                 grind)
              | exact resolve b7e594 b7e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e594
            have b7e596 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b7e595
                 have i₂ := b7e20 x y
                 grind)
              | exact superpose b7e20 b7e595
              | exact resolve b7e595 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e595
            have b7e597 : (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b7e596
                 have i₂ := b7e45
                 grind)
              | exact superpose b7e45 b7e596
              | exact resolve b7e596 b7e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e45 b7e596
            have b7e598 : False := by grind
            exact b7e598
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : x = (M.op y x) := by grind
            have b8e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
            have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X2 (M.op (M.op X1 X0) X1) X3
                 have i₂ := b8e14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e33 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b8e32 X0 X1 x X3
                 have i₂ := b8e14 X0 X1 x
                 grind)
              | exact superpose b8e14 b8e32
              | exact resolve b8e32 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e32
            have b8e37 : x ≠ x ∨ (M.op y y) = (k x y) := by
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
            have b8e41 : (M.op y y) = (k x y) := by grind
            clear b8e37
            have b8e44 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b8e33 y x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e33
              | exact resolve b8e33 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e50 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 X2) = (k (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e17 (M.op X0 X1) X2
                 have i₂ := b8e33 X0 X1 X2
                 grind)
              | exact superpose b8e33 b8e17
              | (have j0 := b8e17 (M.op X0 X1) X2
                 grind)
              | (have r₁ := b8e17 (M.op X0 X1) x
                 have r₂ := b8e33 X0 X1 x
                 grind)
              | exact resolve b8e17 b8e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e54 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have j0 := b8e50 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e50
            have b8e71 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
            have b8e76 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k x X0) := by
              intro X0
              first
              | (have i₁ := b8e17 x X0
                 have i₂ := b8e44 X0
                 grind)
              | exact superpose b8e44 b8e17
              | (have j0 := b8e17 x X0
                 grind)
              | (have r₁ := b8e17 x X0
                 have r₂ := b8e44 X0
                 grind)
              | exact resolve b8e17 b8e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e44
            have b8e79 : ∀ X0 : G, (M.op X0 X0) = (k x X0) := by
              intro X0
              first
              | (have j0 := b8e76 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e76
            have b8e100 : ∀ X0 X1 : G, (k x X0) = (M.op X1 (k x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e33 X0 X0 x
                 have i₂ := b8e79 X0
                 grind)
              | exact superpose b8e79 b8e33
              | exact resolve b8e33 b8e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e105 : ∀ X0 X1 : G, (M.op X0 X1) = (k x (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e33 X0 X1 (M.op X0 X1)
                 have i₂ := b8e79 (M.op X0 X1)
                 grind)
              | exact superpose b8e79 b8e33
              | exact resolve b8e33 b8e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e33
            have b8e411 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op X1 X2)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e29 X0 (M.op X1 X2)
                 have i₂ := b8e54 X1 X2 (τ X0)
                 grind)
              | exact superpose b8e54 b8e29
              | exact resolve b8e29 b8e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e412 : ∀ X0 X1 X2 : G, (σ (k x (τ X0))) = (k (σ (M.op X1 X2)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e411 X0 X1 X2
                 have i₂ := b8e79 (τ X0)
                 grind)
              | exact superpose b8e79 b8e411
              | exact resolve b8e411 b8e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e411
            have b8e429 : ∀ X0 X1 X2 : G, (k (σ x) X0) = (k (σ (M.op X1 X2)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e412 X0 X1 X2
                 have i₂ := b8e29 X0 x
                 grind)
              | exact superpose b8e29 b8e412
              | exact resolve b8e412 b8e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e29 b8e412
            have b8e537 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b8e71 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e71
            have b8e538 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b8e537
                 have r₂ := b8e23
                 grind)
              | exact resolve b8e537 b8e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e537
            have b8e539 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e538
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e538
              | exact resolve b8e538 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e538
            have b8e540 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b8e539
                 have i₂ := b8e41
                 grind)
              | exact superpose b8e41 b8e539
              | exact resolve b8e539 b8e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e41 b8e539
            have b8e1005 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op y y)) X0) := by
              intro X0
              first
              | (have i₁ := b8e54 (σ y) (σ x) X0
                 have i₂ := b8e540
                 grind)
              | exact superpose b8e540 b8e54
              | exact resolve b8e54 b8e540
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e54 b8e540
            have b8e1009 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b8e1005 X0
                 have i₂ := b8e429 X0 y y
                 grind)
              | exact superpose b8e429 b8e1005
              | exact resolve b8e1005 b8e429
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e429 b8e1005
            have b8e1062 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k x X0)) := by
              intro X0
              first
              | (have i₁ := b8e20 x X0
                 have i₂ := b8e1009 (σ X0)
                 grind)
              | exact superpose b8e1009 b8e20
              | exact resolve b8e20 b8e1009
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1009
            have b8e1078 : ∀ X0 : G, (k x (σ X0)) = (σ (k x X0)) := by
              intro X0
              first
              | (have i₁ := b8e1062 X0
                 have i₂ := b8e79 (σ X0)
                 grind)
              | exact superpose b8e79 b8e1062
              | exact resolve b8e1062 b8e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e79 b8e1062
            have b8e1982 : ∀ X0 X1 : G, (σ (k x X0)) = (M.op X1 (σ (k x X0))) := by
              intro X0 X1
              first
              | (have i₁ := b8e100 (σ X0) X1
                 have i₂ := b8e1078 X0
                 grind)
              | exact superpose b8e1078 b8e100
              | exact resolve b8e100 b8e1078
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e100 b8e1078
            have b8e23845 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e1982 (M.op X0 X1) X1
                 have i₂ := b8e105 X0 X1
                 grind)
              | exact superpose b8e105 b8e1982
              | exact resolve b8e1982 b8e105
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e105 b8e1982
            have b8e26582 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b8e23845 y x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e23845
              | exact resolve b8e23845 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e23845
            have b8e27338 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b8e23
                 have i₂ := b8e26582 (σ y)
                 grind)
              | exact superpose b8e26582 b8e23
              | (have r₁ := b8e23
                 have r₂ := b8e26582 (σ y)
                 grind)
              | exact resolve b8e23 b8e26582
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e26582
            have b8e27344 : False := by grind
            exact b8e27344
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
          have b9e33 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
          have b9e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b9e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b9e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b9e37 X0 X1 x X3
               have i₂ := b9e13 X0 X1 x
               grind)
            | exact superpose b9e13 b9e37
            | exact resolve b9e37 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e37
          have b9e39 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X0 (M.op y x) X1
               have i₂ := b9e33 (M.op (M.op y x) X0)
               grind)
            | exact superpose b9e33 b9e13
            | exact resolve b9e13 b9e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e42 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b9e39 x X1
               have i₂ := b9e33 x
               grind)
            | exact superpose b9e33 b9e39
            | exact resolve b9e39 b9e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e33 b9e39
          have b9e45 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
          have b9e48 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear b9e45
          have b9e50 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b9e48
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e48
            | exact resolve b9e48 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e48
          have b9e52 : x = (k x y) ∨ x = (M.op y x) := by grind
          have b9e57 : x = (k x y) := by
            first
            | (have r₁ := b9e52
               have r₂ := b9e21
               grind)
            | exact resolve b9e52 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e52
          have b9e64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b9e19 X1 X0
               have i₂ := b9e18 (σ X1) (σ X0)
               grind)
            | exact superpose b9e18 b9e19
            | (have j1 := b9e18 (σ X1) (σ X0)
               grind)
            | exact resolve b9e19 b9e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e81 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b9e16 y X0
               have i₂ := b9e42 X0
               grind)
            | exact superpose b9e42 b9e16
            | (have j0 := b9e16 y X0
               grind)
            | (have r₁ := b9e16 y x
               have r₂ := b9e42 x
               grind)
            | exact resolve b9e16 b9e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e83 : ∀ X0 : G, (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b9e81 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e81
          have b9e173 : ∀ X0 : G, (σ (k x y)) = (M.op X0 (M.op (σ (k x y)) (σ y))) := by
            intro X0
            first
            | (have i₁ := b9e13 (σ y) (σ y) x
               have i₂ := b9e50
               grind)
            | exact superpose b9e50 b9e13
            | exact resolve b9e13 b9e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e174 : (σ (k x y)) = (M.op (σ (k x y)) (σ y)) := by
            first
            | (have i₁ := b9e173 x
               have i₂ := b9e38 (σ (k x y)) (σ y) x
               grind)
            | exact superpose b9e38 b9e173
            | exact resolve b9e173 b9e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e38 b9e173
          have b9e182 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b9e174
               have i₂ := b9e57
               grind)
            | exact superpose b9e57 b9e174
            | exact resolve b9e174 b9e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e174
          have b9e422 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b9e26
               have i₂ := b9e182
               grind)
            | exact superpose b9e182 b9e26
            | exact resolve b9e26 b9e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26 b9e182
          have b9e589 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b9e64 y y
               have i₂ := b9e50
               grind)
            | exact superpose b9e50 b9e64
            | exact resolve b9e64 b9e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e50 b9e64
          have b9e655 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by grind
          clear b9e589
          have b9e695 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b9e655
               have i₂ := b9e83 y
               grind)
            | exact superpose b9e83 b9e655
            | exact resolve b9e655 b9e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e83 b9e655
          have b9e730 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b9e695
               have i₂ := b9e42 y
               grind)
            | exact superpose b9e42 b9e695
            | exact resolve b9e695 b9e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e42 b9e695
          have b9e731 : (σ y) = (σ (k x y)) := by grind
          clear b9e730
          have b9e748 : (σ x) = (σ y) := by
            first
            | (have i₁ := b9e731
               have i₂ := b9e57
               grind)
            | exact superpose b9e57 b9e731
            | exact resolve b9e731 b9e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e57 b9e731
          have b9e757 : False := by grind
          exact b9e757
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b10e23 : y = (M.op x x) := by grind
            have b10e25 : y ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e32 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
            have b10e36 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b10e14 X0 (M.op y x) X1
                 have i₂ := b10e32 (M.op (M.op y x) X0)
                 grind)
              | exact superpose b10e32 b10e14
              | exact resolve b10e14 b10e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e39 : ∀ X1 : G, y = (M.op X1 y) := by
              intro X1
              first
              | (have i₁ := b10e36 x X1
                 have i₂ := b10e32 x
                 grind)
              | exact superpose b10e32 b10e36
              | exact resolve b10e36 b10e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e32 b10e36
            have b10e48 : y ≠ y := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e39 x
                 grind)
              | exact superpose b10e39 b10e25
              | (have r₁ := b10e25
                 have r₂ := b10e39 x
                 grind)
              | exact resolve b10e25 b10e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e39
            have b10e54 : False := by grind
            exact b10e54
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b11e23 : y = (M.op x x) := by grind
            have b11e25 : y ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e30 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
            have b11e35 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X0 (M.op y x) X1
                 have i₂ := b11e30 (M.op (M.op y x) X0)
                 grind)
              | exact superpose b11e30 b11e14
              | exact resolve b11e14 b11e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e38 : ∀ X1 : G, y = (M.op X1 y) := by
              intro X1
              first
              | (have i₁ := b11e35 x X1
                 have i₂ := b11e30 x
                 grind)
              | exact superpose b11e30 b11e35
              | exact resolve b11e35 b11e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e30 b11e35
            have b11e45 : y ≠ y := by
              first
              | (have i₁ := b11e25
                 have i₂ := b11e38 x
                 grind)
              | exact superpose b11e38 b11e25
              | (have r₁ := b11e25
                 have r₂ := b11e38 x
                 grind)
              | exact resolve b11e25 b11e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e38
            have b11e51 : False := by grind
            exact b11e51
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
            have b12e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e14 X2 (M.op (M.op X1 X0) X1) X3
                 have i₂ := b12e14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b12e35 X0 X1 x X3
                 have i₂ := b12e14 X0 X1 x
                 grind)
              | exact superpose b12e14 b12e35
              | exact resolve b12e35 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e35
            have b12e129 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b12e36 (σ x) (σ x) x
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e36
              | exact resolve b12e36 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e36
            have b12e161 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b12e28
                 have i₂ := b12e129 (σ x)
                 grind)
              | exact superpose b12e129 b12e28
              | (have r₁ := b12e28
                 have r₂ := b12e129 (σ x)
                 grind)
              | exact resolve b12e28 b12e129
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28 b12e129
            have b12e170 : False := by grind
            exact b12e170
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b13e24 : y = (M.op x x) := by grind
              have b13e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e38 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
              have b13e42 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X0 (M.op y x) X1
                   have i₂ := b13e38 (M.op (M.op y x) X0)
                   grind)
                | exact superpose b13e38 b13e15
                | exact resolve b13e15 b13e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e45 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b13e42 x X1
                   have i₂ := b13e38 x
                   grind)
                | exact superpose b13e38 b13e42
                | exact resolve b13e42 b13e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e38 b13e42
              have b13e53 : y ≠ y := by
                first
                | (have i₁ := b13e27
                   have i₂ := b13e45 x
                   grind)
                | exact superpose b13e45 b13e27
                | (have r₁ := b13e27
                   have r₂ := b13e45 x
                   grind)
                | exact resolve b13e27 b13e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e45
              have b13e59 : False := by grind
              exact b13e59
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b14e24 : y = (M.op x x) := by grind
              have b14e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e36 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
              have b14e41 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 (M.op y x) X1
                   have i₂ := b14e36 (M.op (M.op y x) X0)
                   grind)
                | exact superpose b14e36 b14e15
                | exact resolve b14e15 b14e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e44 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b14e41 x X1
                   have i₂ := b14e36 x
                   grind)
                | exact superpose b14e36 b14e41
                | exact resolve b14e41 b14e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e36 b14e41
              have b14e50 : y ≠ y := by
                first
                | (have i₁ := b14e27
                   have i₂ := b14e44 x
                   grind)
                | exact superpose b14e44 b14e27
                | (have r₁ := b14e27
                   have r₂ := b14e44 x
                   grind)
                | exact resolve b14e27 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e44
              have b14e56 : False := by grind
              exact b14e56
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : x ≠ (M.op y x) := by grind
            have b15e23 : y = (M.op x x) := by grind
            have b15e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e46 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b15e49 : x = (k x y) := by
              first
              | (have r₁ := b15e46
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e46 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e46
            have b15e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
            have b15e669 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b15e64 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e64
            have b15e670 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b15e669
                 have r₂ := b15e24
                 grind)
              | exact resolve b15e669 b15e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e669
            have b15e671 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b15e670
                 have i₂ := b15e20 x y
                 grind)
              | exact superpose b15e20 b15e670
              | exact resolve b15e670 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e670
            have b15e672 : (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b15e671
                 have i₂ := b15e49
                 grind)
              | exact superpose b15e49 b15e671
              | exact resolve b15e671 b15e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e49 b15e671
            have b15e673 : False := by grind
            exact b15e673
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b16e24 : y = (M.op x x) := by grind
              have b16e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e36 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
              have b16e41 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X0 (M.op y x) X1
                   have i₂ := b16e36 (M.op (M.op y x) X0)
                   grind)
                | exact superpose b16e36 b16e15
                | exact resolve b16e15 b16e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e44 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b16e41 x X1
                   have i₂ := b16e36 x
                   grind)
                | exact superpose b16e36 b16e41
                | exact resolve b16e41 b16e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e36 b16e41
              have b16e50 : y ≠ y := by
                first
                | (have i₁ := b16e27
                   have i₂ := b16e44 x
                   grind)
                | exact superpose b16e44 b16e27
                | (have r₁ := b16e27
                   have r₂ := b16e44 x
                   grind)
                | exact resolve b16e27 b16e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e44
              have b16e56 : False := by grind
              exact b16e56
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b17e24 : y = (M.op x x) := by grind
              have b17e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e36 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b17e15 x x x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e40 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X0 (M.op y x) X1
                   have i₂ := b17e36 (M.op (M.op y x) X0)
                   grind)
                | exact superpose b17e36 b17e15
                | exact resolve b17e15 b17e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e43 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b17e40 x X1
                   have i₂ := b17e36 x
                   grind)
                | exact superpose b17e36 b17e40
                | exact resolve b17e40 b17e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e36 b17e40
              have b17e47 : y ≠ y := by
                first
                | (have i₁ := b17e27
                   have i₂ := b17e43 x
                   grind)
                | exact superpose b17e43 b17e27
                | (have r₁ := b17e27
                   have r₂ := b17e43 x
                   grind)
                | exact resolve b17e27 b17e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e43
              have b17e53 : False := by grind
              exact b17e53
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b18e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b18e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e36 X0 X1 x X3
               have i₂ := b18e13 X0 X1 x
               grind)
            | exact superpose b18e13 b18e36
            | exact resolve b18e36 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36
          have b18e42 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
          have b18e46 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear b18e42
          have b18e48 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b18e46
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e46
            | exact resolve b18e46 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e46
          have b18e53 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b18e37 x y x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e37
            | exact resolve b18e37 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e19 X1 X0
               have i₂ := b18e18 (σ X1) (σ X0)
               grind)
            | exact superpose b18e18 b18e19
            | (have j1 := b18e18 (σ X1) (σ X0)
               grind)
            | exact resolve b18e19 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e87 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b18e16 y X0
               have i₂ := b18e53 X0
               grind)
            | exact superpose b18e53 b18e16
            | (have j0 := b18e16 y X0
               grind)
            | (have r₁ := b18e16 y X0
               have r₂ := b18e53 X0
               grind)
            | exact resolve b18e16 b18e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e89 : ∀ X0 : G, (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b18e87 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e87
          have b18e112 : ∀ X0 : G, (σ (k x y)) = (M.op X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b18e37 (σ y) (σ y) x
               have i₂ := b18e48
               grind)
            | exact superpose b18e48 b18e37
            | exact resolve b18e37 b18e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e37
          have b18e644 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b18e72 y y
               have i₂ := b18e48
               grind)
            | exact superpose b18e48 b18e72
            | exact resolve b18e72 b18e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e48 b18e72
          have b18e725 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by grind
          clear b18e644
          have b18e773 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b18e725
               have i₂ := b18e89 y
               grind)
            | exact superpose b18e89 b18e725
            | exact resolve b18e725 b18e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e89 b18e725
          have b18e819 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b18e773
               have i₂ := b18e53 y
               grind)
            | exact superpose b18e53 b18e773
            | exact resolve b18e773 b18e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e53 b18e773
          have b18e820 : (σ y) = (σ (k x y)) := by grind
          clear b18e819
          have b18e1060 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e112 X0
               have i₂ := b18e820
               grind)
            | exact superpose b18e820 b18e112
            | exact resolve b18e112 b18e820
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e112 b18e820
          have b18e1235 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b18e26
               have i₂ := b18e1060 (σ x)
               grind)
            | exact superpose b18e1060 b18e26
            | (have r₁ := b18e26
               have r₂ := b18e1060 (σ x)
               grind)
            | exact resolve b18e26 b18e1060
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e26 b18e1060
          have b18e1257 : False := by grind
          exact b18e1257
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b19e22 : x ≠ (M.op y x) := by grind
            have b19e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e30 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
            have b19e35 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X0 (M.op x y) X1
                 have i₂ := b19e30 (M.op (M.op x y) X0)
                 grind)
              | exact superpose b19e30 b19e14
              | exact resolve b19e14 b19e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e38 : ∀ X1 : G, x = (M.op X1 x) := by
              intro X1
              first
              | (have i₁ := b19e35 x X1
                 have i₂ := b19e30 x
                 grind)
              | exact superpose b19e30 b19e35
              | exact resolve b19e35 b19e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30 b19e35
            have b19e45 : x ≠ x := by
              first
              | (have i₁ := b19e22
                 have i₂ := b19e38 y
                 grind)
              | exact superpose b19e38 b19e22
              | (have r₁ := b19e22
                 have r₂ := b19e38 y
                 grind)
              | exact resolve b19e22 b19e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e38
            have b19e51 : False := by grind
            exact b19e51
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : x ≠ (M.op y x) := by grind
            have b20e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
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
            have b20e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 X2 (M.op (M.op X1 X0) X1) X3
                 have i₂ := b20e14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e33 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b20e32 X0 X1 x X3
                 have i₂ := b20e14 X0 X1 x
                 grind)
              | exact superpose b20e14 b20e32
              | exact resolve b20e32 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e32
            have b20e34 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b20e33 (σ y) (σ x) x
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e33
              | exact resolve b20e33 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e49 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b20e17 (σ x) X0
                 have i₂ := b20e34 X0
                 grind)
              | exact superpose b20e34 b20e17
              | (have j0 := b20e17 (σ x) X0
                 grind)
              | (have r₁ := b20e17 (σ x) X0
                 have r₂ := b20e34 X0
                 grind)
              | exact resolve b20e17 b20e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e52 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) X0) := by
              intro X0
              first
              | (have j0 := b20e49 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e49
            have b20e160 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
            have b20e391 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b20e160 x X0
                 have i₂ := b20e52 X0
                 grind)
              | exact superpose b20e52 b20e160
              | exact resolve b20e160 b20e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e52 b20e160
            have b20e427 : (τ (σ x)) = (k x (τ (σ x))) := by
              first
              | (have i₁ := b20e391 (σ x)
                 have i₂ := b20e34 (σ x)
                 grind)
              | exact superpose b20e34 b20e391
              | exact resolve b20e391 b20e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e34 b20e391
            have b20e439 : x = (k x x) := by
              first
              | (have i₁ := b20e427
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e427
              | exact resolve b20e427 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e427
            have b20e464 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b20e19 x x
                 have i₂ := b20e439
                 grind)
              | exact superpose b20e439 b20e19
              | (have j0 := b20e19 x x
                 grind)
              | exact resolve b20e19 b20e439
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e439
            have b20e465 : x = (M.op x x) := by grind
            clear b20e464
            have b20e478 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b20e33 x x x
                 have i₂ := b20e465
                 grind)
              | exact superpose b20e465 b20e33
              | exact resolve b20e33 b20e465
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e33 b20e465
            have b20e591 : x ≠ x := by
              first
              | (have i₁ := b20e22
                 have i₂ := b20e478 y
                 grind)
              | exact superpose b20e478 b20e22
              | (have r₁ := b20e22
                 have r₂ := b20e478 y
                 grind)
              | exact resolve b20e22 b20e478
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e478
            have b20e607 : False := by grind
            exact b20e607
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : x ≠ (M.op y x) := by grind
            have b21e23 : y ≠ (M.op x x) := by grind
            have b21e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b21e25 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e46 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b21e49 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e46
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e46 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e46
            have b21e50 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e49
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e49
              | exact resolve b21e49 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e49
            have b21e53 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e50
                 grind)
              | exact superpose b21e50 b21e15
              | exact resolve b21e15 b21e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e50
            have b21e54 : x = (k x y) := by
              first
              | (have i₁ := b21e53
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e53
              | exact resolve b21e53 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e53
            have b21e77 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e54
                 grind)
              | exact superpose b21e54 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e54
            have b21e78 : x = (M.op y x) ∨ y = (M.op x x) := by grind
            clear b21e77
            have b21e80 : y = (M.op x x) := by
              first
              | (have r₁ := b21e78
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e78 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e78
            have b21e82 : False := by grind
            exact b21e82
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b22e23 : x ≠ (M.op y x) := by grind
              have b22e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e36 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
              have b22e41 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X0 (M.op x y) X1
                   have i₂ := b22e36 (M.op (M.op x y) X0)
                   grind)
                | exact superpose b22e36 b22e15
                | exact resolve b22e15 b22e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e44 : ∀ X1 : G, x = (M.op X1 x) := by
                intro X1
                first
                | (have i₁ := b22e41 x X1
                   have i₂ := b22e36 x
                   grind)
                | exact superpose b22e36 b22e41
                | exact resolve b22e41 b22e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e36 b22e41
              have b22e50 : x ≠ x := by
                first
                | (have i₁ := b22e23
                   have i₂ := b22e44 y
                   grind)
                | exact superpose b22e44 b22e23
                | (have r₁ := b22e23
                   have r₂ := b22e44 y
                   grind)
                | exact resolve b22e23 b22e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e44
              have b22e56 : False := by grind
              exact b22e56
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : x ≠ (M.op y x) := by grind
              have b23e24 : y ≠ (M.op x x) := by grind
              have b23e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b23e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e60 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
              have b23e66 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e60
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e60 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e60
              have b23e68 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b23e66
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e66
                | exact resolve b23e66 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e66
              have b23e71 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e68
                   grind)
                | exact superpose b23e68 b23e16
                | exact resolve b23e16 b23e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e68
              have b23e72 : x = (k x y) := by
                first
                | (have i₁ := b23e71
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e71
                | exact resolve b23e71 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e71
              have b23e97 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e72
                   grind)
                | exact superpose b23e72 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e72
              have b23e98 : x = (M.op y x) ∨ y = (M.op x x) := by grind
              clear b23e97
              have b23e100 : y = (M.op x x) := by
                first
                | (have r₁ := b23e98
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e98 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e98
              have b23e102 : False := by grind
              exact b23e102
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b24e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
            have b24e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X2 (M.op (M.op X1 X0) X1) X3
                 have i₂ := b24e14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e34 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b24e33 X0 X1 x X3
                 have i₂ := b24e14 X0 X1 x
                 grind)
              | exact superpose b24e14 b24e33
              | exact resolve b24e33 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33
            have b24e45 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b24e34 x y x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e34
              | exact resolve b24e34 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 X0
                 have i₂ := b24e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b24e19 b24e20
              | (have j1 := b24e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b24e20 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e78 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k y X0) := by
              intro X0
              first
              | (have i₁ := b24e17 y X0
                 have i₂ := b24e45 X0
                 grind)
              | exact superpose b24e45 b24e17
              | (have j0 := b24e17 y X0
                 grind)
              | (have r₁ := b24e17 y X0
                 have r₂ := b24e45 X0
                 grind)
              | exact resolve b24e17 b24e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e80 : ∀ X0 : G, (M.op X0 X0) = (k y X0) := by
              intro X0
              first
              | (have j0 := b24e78 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e78
            have b24e101 : ∀ X0 X1 : G, (k y X0) = (M.op X1 (k y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e34 X0 X0 x
                 have i₂ := b24e80 X0
                 grind)
              | exact superpose b24e80 b24e34
              | exact resolve b24e34 b24e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e34
            have b24e647 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b24e63 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e63
            have b24e649 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b24e647 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e647
            have b24e664 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k y (σ X0)) := by
              intro X0
              first
              | (have i₁ := b24e649 X0
                 have i₂ := b24e80 (σ X0)
                 grind)
              | exact superpose b24e80 b24e649
              | (have j0 := b24e649 X0
                 grind)
              | exact resolve b24e649 b24e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e649
            have b24e1023 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (k y (σ y)) := by
              first
              | (have i₁ := b24e664 y
                 have i₂ := b24e80 y
                 grind)
              | exact superpose b24e80 b24e664
              | (have j0 := b24e664 y
                 grind)
              | exact resolve b24e664 b24e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e80 b24e664
            have b24e1032 : (σ y) ≠ (σ y) ∨ (σ y) = (k y (σ y)) := by
              first
              | (have i₁ := b24e1023
                 have i₂ := b24e45 y
                 grind)
              | exact superpose b24e45 b24e1023
              | exact resolve b24e1023 b24e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e45 b24e1023
            have b24e1033 : (σ y) = (k y (σ y)) := by grind
            clear b24e1032
            have b24e1054 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b24e101 (σ y) x
                 have i₂ := b24e1033
                 grind)
              | exact superpose b24e1033 b24e101
              | exact resolve b24e101 b24e1033
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e101 b24e1033
            have b24e1138 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b24e28
                 have i₂ := b24e1054 (σ x)
                 grind)
              | exact superpose b24e1054 b24e28
              | (have r₁ := b24e28
                 have r₂ := b24e1054 (σ x)
                 grind)
              | exact resolve b24e28 b24e1054
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e28 b24e1054
            have b24e1161 : False := by grind
            exact b24e1161
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b25e23 : x ≠ (M.op y x) := by grind
              have b25e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e36 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
                intro X0
                first
                | (have i₁ := b25e15 y y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e40 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X0 (M.op x y) X1
                   have i₂ := b25e36 (M.op (M.op x y) X0)
                   grind)
                | exact superpose b25e36 b25e15
                | exact resolve b25e15 b25e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e43 : ∀ X1 : G, x = (M.op X1 x) := by
                intro X1
                first
                | (have i₁ := b25e40 x X1
                   have i₂ := b25e36 x
                   grind)
                | exact superpose b25e36 b25e40
                | exact resolve b25e40 b25e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e36 b25e40
              have b25e47 : x ≠ x := by
                first
                | (have i₁ := b25e23
                   have i₂ := b25e43 y
                   grind)
                | exact superpose b25e43 b25e23
                | (have r₁ := b25e23
                   have r₂ := b25e43 y
                   grind)
                | exact resolve b25e23 b25e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e43
              have b25e53 : False := by grind
              exact b25e53
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
              have b26e27 : y ≠ (M.op x y) := by grind
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
              have b26e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X2 (M.op (M.op X1 X0) X1) X3
                   have i₂ := b26e15 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e37 X0 X1 x X3
                   have i₂ := b26e15 X0 X1 x
                   grind)
                | exact superpose b26e15 b26e37
                | exact resolve b26e37 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e37
              have b26e47 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 X2) = (k (M.op X0 X1) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e18 (M.op X0 X1) X2
                   have i₂ := b26e38 X0 X1 X2
                   grind)
                | exact superpose b26e38 b26e18
                | (have j0 := b26e18 (M.op X0 X1) X2
                   grind)
                | (have r₁ := b26e18 (M.op X0 X1) x
                   have r₂ := b26e38 X0 X1 x
                   grind)
                | exact resolve b26e18 b26e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e48 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X1) X2) := by
                intro X0 X1 X2
                first
                | (have j0 := b26e47 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e47
              have b26e96 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e100 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e38 X0 X0 x
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e38 X0 X1 x
                   have i₂ := b26e20 X0 (M.op X0 X1)
                   grind)
                | exact superpose b26e20 b26e38
                | (have j1 := b26e20 X1 X0
                   grind)
                | exact resolve b26e38 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e104 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
              have b26e105 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e96 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e96
              have b26e114 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
              clear b26e31
              have b26e256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e105 (σ X1) (σ X0)
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e105
                | (have j0 := b26e105 (σ X1) (σ X0)
                   grind)
                | exact resolve b26e105 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e105
              have b26e300 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b26e104 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e104
              have b26e301 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b26e300
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e300 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e300
              have b26e302 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e301
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e301
                | exact resolve b26e301 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e301
              have b26e310 : ∀ X0 : G, (M.op X0 X0) = (k (σ (k x y)) X0) := by
                intro X0
                first
                | (have i₁ := b26e48 (σ y) (σ x) X0
                   have i₂ := b26e302
                   grind)
                | exact superpose b26e302 b26e48
                | exact resolve b26e48 b26e302
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e302
              have b26e484 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op y x)) X0) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                intro X0
                first
                | (have i₁ := b26e310 X0
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e310
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e310 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e310
              have b26e532 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op y x)) X0) ∨ x = (M.op y x) := by
                intro X0
                first
                | (have j0 := b26e484 X0
                   grind)
                | (have r₁ := b26e484 X0
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e484 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e484
              have b26e544 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op y x)) X0) := by
                intro X0
                first
                | (have j0 := b26e532 X0
                   grind)
                | (have r₁ := b26e532 X0
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e532 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e532
              have b26e619 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (M.op y x) (τ X0)) := by
                intro X0
                first
                | (have i₁ := b26e114 (M.op y x) X0
                   have i₂ := b26e544 X0
                   grind)
                | exact superpose b26e544 b26e114
                | exact resolve b26e114 b26e544
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e114 b26e544
              have b26e1106 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X0 X3) = (k X3 X0) ∨ (M.op X0 X3) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X1 X0 X2
                   have i₂ := b26e100 X0 X3 (M.op X0 X1)
                   grind)
                | exact superpose b26e100 b26e15
                | (have j1 := b26e100 X0 X3 X2
                   grind)
                | exact resolve b26e15 b26e100
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1706 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e48 y x (τ X0)
                   have i₂ := b26e619 X0
                   grind)
                | exact superpose b26e619 b26e48
                | exact resolve b26e48 b26e619
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e48 b26e619
              have b26e2211 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e38 (τ X0) (τ X0) x
                   have i₂ := b26e1706 X0
                   grind)
                | exact superpose b26e1706 b26e38
                | exact resolve b26e38 b26e1706
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1706
              have b26e2959 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e256 y x
                   grind)
                | exact superpose b26e256 b26e22
                | (have j1 := b26e256 y x
                   grind)
                | exact resolve b26e22 b26e256
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e256
              have b26e11165 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e2211 (M.op X0 X1) X1
                   have i₂ := b26e38 X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b26e38 b26e2211
                | exact resolve b26e2211 b26e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38 b26e2211
              have b26e66175 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e23
                   have i₂ := b26e1106 x y X0 X1
                   grind)
                | (have i₁ := b26e23
                   have i₂ := b26e1106 x X0 y X1
                   grind)
                | exact superpose b26e1106 b26e23
                | (have j1 := b26e1106 x X1 x X1
                   grind)
                | (have r₁ := b26e23
                   have r₂ := b26e1106 y X1 x x
                   grind)
                | exact resolve b26e23 b26e1106
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1106
              have b26e66413 : ∀ X1 : G, (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X1
                first
                | (have j0 := b26e66175 x X1
                   have j1 := b26e100 x X1 x
                   grind)
                | (have r₁ := b26e66175 x X1
                   have r₂ := b26e100 x X1 x
                   grind)
                | (have r₁ := b26e66175 x X1
                   have r₂ := b26e100 x x x
                   grind)
                | exact resolve b26e66175 b26e100
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e100 b26e66175
              have b26e183362 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b26e2959
                   have i₂ := b26e66413 y
                   grind)
                | exact superpose b26e66413 b26e2959
                | (have j1 := b26e66413 y
                   grind)
                | exact resolve b26e2959 b26e66413
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2959 b26e66413
              have b26e183389 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
              clear b26e183362
              have b26e183398 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
                first
                | (have r₁ := b26e183389
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e183389 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e183389
              have b26e512853 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
                intro X0
                first
                | (have i₁ := b26e11165 (σ x) (σ y) x
                   have i₂ := b26e183398
                   grind)
                | exact superpose b26e183398 b26e11165
                | exact resolve b26e11165 b26e183398
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11165 b26e183398
              have b26e512937 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) := by
                intro X0
                first
                | (have i₁ := b26e512853 X0
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e512853
                | exact resolve b26e512853 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e512853
              have b26e514529 : ∀ X0 : G, (M.op x y) = (τ (σ y)) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b26e16 (M.op x y)
                   have i₂ := b26e512937 X0
                   grind)
                | exact superpose b26e512937 b26e16
                | (have j1 := b26e512937 X0
                   grind)
                | exact resolve b26e16 b26e512937
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e512937
              have b26e514607 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b26e514529 X0
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e514529
                | (have j0 := b26e514529 x
                   grind)
                | exact resolve b26e514529 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e514529
              have b26e514741 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have j0 := b26e514607 X0
                   grind)
                | (have r₁ := b26e514607 X0
                   have r₂ := b26e27
                   grind)
                | (have r₁ := b26e514607 x
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e514607 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e514607
              have b26e516093 : y ≠ y := by
                first
                | (have i₁ := b26e27
                   have i₂ := b26e514741 x
                   grind)
                | exact superpose b26e514741 b26e27
                | (have r₁ := b26e27
                   have r₂ := b26e514741 x
                   grind)
                | exact resolve b26e27 b26e514741
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e514741
              have b26e516395 : False := by grind
              exact b26e516395

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_y_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e11 y y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) (σ y) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e30 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e30
        | exact resolve b0e30 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e36 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e29 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e29
        | exact resolve b0e29 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e48 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e35 (σ x)
           grind)
        | exact superpose b0e35 b0e18
        | exact resolve b0e18 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e50 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e48
           have i₂ := b0e36 x
           grind)
        | exact superpose b0e36 b0e48
        | exact resolve b0e48 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e48
      have b0e51 : False := by grind
      exact b0e51
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e24 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b1e25 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e28 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b1e12 y y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e28 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e28
          | exact resolve b1e28 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e35 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e34 x
             grind)
          | exact superpose b1e34 b1e23
          | exact resolve b1e23 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e34
        have b1e41 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e44 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e41
        have b1e45 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e44
             have r₂ := b1e21
             grind)
          | exact resolve b1e44 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e46 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e45
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e45
          | exact resolve b1e45 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e47 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e25 x
             grind)
          | exact superpose b1e25 b1e46
          | exact resolve b1e46 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e46
        have b1e48 : False := by grind
        exact b1e48
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b2e24 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23
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
        have b2e77 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 y
             have i₂ := b2e24 (τ X0)
             grind)
          | exact superpose b2e24 b2e25
          | exact resolve b2e25 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e25
        have b2e84 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e77 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e77
          | exact resolve b2e77 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e87 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e17 X0 (σ y)
             have i₂ := b2e84 X0
             grind)
          | exact superpose b2e84 b2e17
          | (have j0 := b2e17 X0 (σ y)
             grind)
          | exact resolve b2e17 b2e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e90 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e87 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e93 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e90 X0
             grind)
          | (have r₁ := b2e90 (σ y)
             have r₂ := b2e21
             grind)
          | (have r₁ := b2e90 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e90 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e112 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e93 (σ x)
             grind)
          | exact superpose b2e93 b2e22
          | (have r₁ := b2e22
             have r₂ := b2e93 (σ x)
             grind)
          | exact resolve b2e22 b2e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93
        have b2e113 : False := by grind
        exact b2e113
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e24 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
        have b3e25 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b3e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e29 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e25 (σ X0)
             grind)
          | exact superpose b3e25 b3e18
          | exact resolve b3e18 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e31 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) (σ y) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e31 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e31
          | exact resolve b3e31 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e37 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e36 (σ x)
             grind)
          | exact superpose b3e36 b3e23
          | exact resolve b3e23 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e36
        have b3e43 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
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
        have b3e46 : y = (M.op y y) ∨ y = (k x y) := by grind
        clear b3e43
        have b3e47 : y = (k x y) := by
          first
          | (have r₁ := b3e46
             have r₂ := b3e20
             grind)
          | exact resolve b3e46 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e78 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29 x
             have i₂ := b3e47
             grind)
          | exact superpose b3e47 b3e29
          | exact resolve b3e29 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e47
        have b3e87 : False := by grind
        exact b3e87
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b5e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e34 X0 X1 x X3
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e34
            | exact resolve b5e34 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e42 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
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
          have b5e45 : y = (M.op y y) ∨ y = (k x y) := by grind
          clear b5e42
          have b5e46 : y = (k x y) := by
            first
            | (have r₁ := b5e45
               have r₂ := b5e21
               grind)
            | exact resolve b5e45 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X1) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e407 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e36 (σ X0) (σ X1) x
               have i₂ := b5e51 X0 X1
               grind)
            | exact superpose b5e51 b5e36
            | (have j1 := b5e51 X1 X1
               grind)
            | exact resolve b5e36 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e51
          have b5e3524 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e407 x y x
               have i₂ := b5e46
               grind)
            | exact superpose b5e46 b5e407
            | (have j0 := b5e407 y y x
               grind)
            | exact resolve b5e407 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e407
          have b5e3617 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e3524 X0
               grind)
            | (have r₁ := b5e3524 (σ y)
               have r₂ := b5e23
               grind)
            | (have r₁ := b5e3524 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e3524 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3524
          have b5e3634 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e3617 X0
               grind)
            | (have r₁ := b5e3617 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e3617 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3617
          have b5e3648 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e3634 (σ y)
               grind)
            | exact superpose b5e3634 b5e23
            | (have r₁ := b5e23
               have r₂ := b5e3634 (σ y)
               grind)
            | exact resolve b5e23 b5e3634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3634
          have b5e3684 : False := by grind
          exact b5e3684
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
        have b6e24 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e28 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e24 (σ X0)
             have i₂ := b6e18 X0 y
             grind)
          | exact superpose b6e18 b6e24
          | exact resolve b6e24 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e31 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e28 X0
             grind)
          | exact superpose b6e28 b6e13
          | exact resolve b6e13 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e32 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e31 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e55 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 X0 y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e61 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
          intro X0
          first
          | (have j0 := b6e55 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e68 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b6e61 X0
             grind)
          | (have r₁ := b6e61 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e61 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e61 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e75 : x ≠ x := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e68 x
             grind)
          | exact superpose b6e68 b6e21
          | (have r₁ := b6e21
             have r₂ := b6e68 x
             grind)
          | exact resolve b6e21 b6e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e82 : False := by grind
        exact b6e82
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y y) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b7e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e30 X0 X1 x X3
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e43 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e47 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e48 : (σ y) = (σ (k x y)) := by
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
          have b7e51 : (k x y) = (τ (σ y)) := by
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
          have b7e52 : y = (k x y) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e51
            | exact resolve b7e51 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e70 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e52
               grind)
            | exact superpose b7e52 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e71 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e21
               grind)
            | exact resolve b7e70 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e73 : y = (M.op x y) := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e22
               grind)
            | exact resolve b7e71 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e83 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e32 x y x
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e32
            | exact resolve b7e32 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e73
          have b7e232 : y ≠ y := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e83 y
               grind)
            | exact superpose b7e83 b7e21
            | (have r₁ := b7e21
               have r₂ := b7e83 y
               grind)
            | exact resolve b7e21 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e246 : False := by grind
          exact b7e246
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e312 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e47 x y
               grind)
            | exact superpose b8e47 b8e20
            | (have j1 := b8e47 y y
               grind)
            | exact resolve b8e20 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47
          have b8e357 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e312
               have r₂ := b8e23
               grind)
            | exact resolve b8e312 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e312
          have b8e362 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e357
               have r₂ := b8e24
               grind)
            | exact resolve b8e357 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e357
          have b8e363 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e362
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e362
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e362 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e362
          have b8e364 : y = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b8e363
          have b8e365 : x = (M.op x y) := by
            first
            | (have r₁ := b8e364
               have r₂ := b8e21
               grind)
            | exact resolve b8e364 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e364
          have b8e366 : False := by grind
          exact b8e366

/-- `Equation3601`: `x ◇ y = z ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pyx_Equation3601 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3601 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3601.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op y y) := by grind
        have b0e21 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e38 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e15 X0 (σ y)
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e15
          | (have j0 := b0e15 X0 (σ y)
             grind)
          | (have r₁ := b0e15 X0 (σ y)
             have r₂ := b0e21
             grind)
          | exact resolve b0e15 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e40 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b0e15 X0 y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e15
          | (have j0 := b0e15 X0 y
             grind)
          | (have r₁ := b0e15 X0 y
             have r₂ := b0e20
             grind)
          | exact resolve b0e15 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b0e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40
        have b0e43 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b0e38 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38
        have b0e89 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e18 X0 y
             have i₂ := b0e43 (σ X0)
             grind)
          | exact superpose b0e43 b0e18
          | exact resolve b0e18 b0e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e43
        have b0e91 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b0e89 X0
             have i₂ := b0e41 X0
             grind)
          | exact superpose b0e41 b0e89
          | exact resolve b0e89 b0e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41 b0e89
        have b0e678 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e91 x
             grind)
          | exact superpose b0e91 b0e19
          | (have r₁ := b0e19
             have r₂ := b0e91 x
             grind)
          | exact resolve b0e19 b0e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e91
        have b0e696 : False := by grind
        exact b0e696
      · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
        · have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : y = (M.op y y) := by grind
          have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e46 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b1e16 X0 y
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e16
            | (have j0 := b1e16 X0 y
               grind)
            | (have r₁ := b1e16 X0 y
               have r₂ := b1e21
               grind)
            | exact resolve b1e16 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e47 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b1e16 X0 (σ y)
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e16
            | (have j0 := b1e16 X0 (σ y)
               grind)
            | (have r₁ := b1e16 X0 (σ y)
               have r₂ := b1e22
               grind)
            | exact resolve b1e16 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e48 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b1e47 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e47
          have b1e49 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b1e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e46
          have b1e119 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b1e19 X0 y
               have i₂ := b1e48 (σ X0)
               grind)
            | exact superpose b1e48 b1e19
            | exact resolve b1e19 b1e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e48
          have b1e121 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b1e119 X0
               have i₂ := b1e49 X0
               grind)
            | exact superpose b1e49 b1e119
            | exact resolve b1e119 b1e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e49 b1e119
          have b1e710 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e121 x
               grind)
            | exact superpose b1e121 b1e20
            | (have r₁ := b1e20
               have r₂ := b1e121 x
               grind)
            | exact resolve b1e20 b1e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e121
          have b1e728 : False := by grind
          exact b1e728
        · have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op y y) := by grind
          have b2e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e43 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b2e16 X0 y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e16
            | (have j0 := b2e16 X0 y
               grind)
            | (have r₁ := b2e16 X0 y
               have r₂ := b2e21
               grind)
            | exact resolve b2e16 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e44 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b2e16 X0 (σ y)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e16
            | (have j0 := b2e16 X0 (σ y)
               grind)
            | (have r₁ := b2e16 X0 (σ y)
               have r₂ := b2e22
               grind)
            | exact resolve b2e16 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e45 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b2e44 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e44
          have b2e46 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b2e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e43
          have b2e80 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b2e19 X0 y
               have i₂ := b2e45 (σ X0)
               grind)
            | exact superpose b2e45 b2e19
            | exact resolve b2e19 b2e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e45
          have b2e83 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b2e80 X0
               have i₂ := b2e46 X0
               grind)
            | exact superpose b2e46 b2e80
            | exact resolve b2e80 b2e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e46 b2e80
          have b2e569 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e83 x
               grind)
            | exact superpose b2e83 b2e20
            | (have r₁ := b2e20
               have r₂ := b2e83 x
               grind)
            | exact resolve b2e20 b2e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e83
          have b2e587 : False := by grind
          exact b2e587
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : y = (M.op y y) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b3e23 : (σ x) = (M.op (σ x) (σ y)) := by grind
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
          have b3e46 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
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
          have b3e47 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b3e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e46
          have b3e61 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b3e62 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b3e61
          have b3e63 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e62
               have r₂ := b3e22
               grind)
            | exact resolve b3e62 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e62
          have b3e64 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b3e63
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e63
            | exact resolve b3e63 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e63
          have b3e65 : (σ (M.op x y)) = (σ x) := by
            first
            | (have i₁ := b3e64
               have i₂ := b3e47 x
               grind)
            | exact superpose b3e47 b3e64
            | exact resolve b3e64 b3e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e47 b3e64
          have b3e66 : False := by grind
          exact b3e66
        · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
          · have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b4e22 : y = (M.op y y) := by grind
            have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b4e21
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e21
              | exact resolve b4e21 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e45 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b4e17 X0 y
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e17
              | (have j0 := b4e17 X0 y
                 grind)
              | (have r₁ := b4e17 X0 y
                 have r₂ := b4e22
                 grind)
              | exact resolve b4e17 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e46 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
              intro X0
              first
              | (have j0 := b4e45 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e45
            have b4e52 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b4e56 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b4e52
            have b4e58 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e56
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e56 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e56
            have b4e59 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b4e58
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e58
              | exact resolve b4e58 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e58
            have b4e60 : (σ (M.op x y)) = (σ x) := by
              first
              | (have i₁ := b4e59
                 have i₂ := b4e46 x
                 grind)
              | exact superpose b4e46 b4e59
              | exact resolve b4e59 b4e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e46 b4e59
            have b4e61 : False := by grind
            exact b4e61
          · have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b5e22 : y = (M.op y y) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b5e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e27 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b5e21
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e21
              | exact resolve b5e21 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e42 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
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
            have b5e43 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
              intro X0
              first
              | (have j0 := b5e42 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e42
            have b5e44 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b5e47 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b5e44
            have b5e48 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e47
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e47 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e47
            have b5e49 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b5e48
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e48
              | exact resolve b5e48 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e48
            have b5e50 : (σ (M.op x y)) = (σ x) := by
              first
              | (have i₁ := b5e49
                 have i₂ := b5e43 x
                 grind)
              | exact superpose b5e43 b5e49
              | exact resolve b5e49 b5e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e43 b5e49
            have b5e51 : False := by grind
            exact b5e51
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op y y) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e43 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
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
          have b6e46 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b6e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e43
          have b6e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X1 X0
               have i₂ := b6e18 (σ X1) (σ X0)
               grind)
            | exact superpose b6e18 b6e19
            | (have j1 := b6e18 (σ X0) (σ X0)
               grind)
            | exact resolve b6e19 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e354 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b6e62 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e62
          have b6e355 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b6e354 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e354
          have b6e2747 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b6e355 y
               have i₂ := b6e46 y
               grind)
            | exact superpose b6e46 b6e355
            | (have j0 := b6e355 y
               grind)
            | exact resolve b6e355 b6e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e46 b6e355
          have b6e2756 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have r₁ := b6e2747
               have r₂ := b6e22
               grind)
            | exact resolve b6e2747 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2747
          have b6e2763 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b6e2756
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e2756
            | exact resolve b6e2756 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2756
          have b6e2764 : False := by grind
          exact b6e2764
        · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
          · have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e22 : y = (M.op y y) := by grind
            have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e43 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b7e17 X0 y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e17
              | (have j0 := b7e17 X0 y
                 grind)
              | (have r₁ := b7e17 X0 y
                 have r₂ := b7e22
                 grind)
              | exact resolve b7e17 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e44 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
              intro X0
              first
              | (have j0 := b7e43 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e43
            have b7e55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 X1 X0
                 have i₂ := b7e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b7e19 b7e20
              | (have j1 := b7e19 (σ X0) (σ X0)
                 grind)
              | exact resolve b7e20 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e412 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b7e55 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e55
            have b7e413 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b7e412 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e412
            have b7e2156 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b7e413 y
                 have i₂ := b7e44 y
                 grind)
              | exact superpose b7e44 b7e413
              | (have j0 := b7e413 y
                 grind)
              | exact resolve b7e413 b7e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e44 b7e413
            have b7e2165 : (σ y) ≠ (σ (M.op y y)) := by
              first
              | (have r₁ := b7e2156
                 have r₂ := b7e23
                 grind)
              | exact resolve b7e2156 b7e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e2156
            have b7e2170 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b7e2165
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e2165
              | exact resolve b7e2165 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e2165
            have b7e2171 : False := by grind
            exact b7e2171
          · have b8e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op y y) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e40 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
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
            have b8e41 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
              intro X0
              first
              | (have j0 := b8e40 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e40
            have b8e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X1 X0
                 have i₂ := b8e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b8e19 b8e20
              | (have j1 := b8e19 (σ X0) (σ X0)
                 grind)
              | exact resolve b8e20 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e384 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b8e52 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e52
            have b8e385 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b8e384 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e384
            have b8e1706 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b8e385 y
                 have i₂ := b8e41 y
                 grind)
              | exact superpose b8e41 b8e385
              | (have j0 := b8e385 y
                 grind)
              | exact resolve b8e385 b8e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e41 b8e385
            have b8e1715 : (σ y) ≠ (σ (M.op y y)) := by
              first
              | (have r₁ := b8e1706
                 have r₂ := b8e23
                 grind)
              | exact resolve b8e1706 b8e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1706
            have b8e1720 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b8e1715
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e1715
              | exact resolve b8e1715 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1715
            have b8e1721 : False := by grind
            exact b8e1721
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : y ≠ (M.op y y) := by grind
          have b9e22 : x = (M.op x y) := by grind
          have b9e23 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e20
            | exact resolve b9e20 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e41 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b9e44 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b9e41 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e41
          have b9e55 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
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
          have b9e57 : y = (M.op y y) ∨ x = (k x y) := by grind
          clear b9e55
          have b9e58 : x = (k x y) := by
            first
            | (have r₁ := b9e57
               have r₂ := b9e21
               grind)
            | exact resolve b9e57 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e57
          have b9e93 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b9e19 X0 y
               have i₂ := b9e44 (σ X0)
               grind)
            | exact superpose b9e44 b9e19
            | exact resolve b9e19 b9e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e44
          have b9e618 : (σ x) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b9e25
               have i₂ := b9e93 x
               grind)
            | exact superpose b9e93 b9e25
            | exact resolve b9e25 b9e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e25 b9e93
          have b9e641 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b9e618
               have i₂ := b9e58
               grind)
            | exact superpose b9e58 b9e618
            | exact resolve b9e618 b9e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e58 b9e618
          have b9e642 : False := by grind
          exact b9e642
        · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
          · have b10e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b10e22 : y ≠ (M.op y y) := by grind
            have b10e23 : x = (M.op x y) := by grind
            have b10e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e27 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b10e21
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e21
              | exact resolve b10e21 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e44 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
            have b10e45 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have j0 := b10e44 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e44
            have b10e58 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
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
            have b10e61 : y = (M.op y y) ∨ x = (k x y) := by grind
            clear b10e58
            have b10e63 : x = (k x y) := by
              first
              | (have r₁ := b10e61
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e61 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e61
            have b10e95 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
              intro X0
              first
              | (have i₁ := b10e20 X0 y
                 have i₂ := b10e45 (σ X0)
                 grind)
              | exact superpose b10e45 b10e20
              | exact resolve b10e20 b10e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e45
            have b10e752 : (σ x) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b10e27
                 have i₂ := b10e95 x
                 grind)
              | exact superpose b10e95 b10e27
              | exact resolve b10e27 b10e95
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e27 b10e95
            have b10e775 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b10e752
                 have i₂ := b10e63
                 grind)
              | exact superpose b10e63 b10e752
              | exact resolve b10e752 b10e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e63 b10e752
            have b10e776 : False := by grind
            exact b10e776
          · have b11e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b11e22 : y ≠ (M.op y y) := by grind
            have b11e23 : x = (M.op x y) := by grind
            have b11e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b11e21
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e21
              | exact resolve b11e21 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e41 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
            have b11e42 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have j0 := b11e41 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e41
            have b11e51 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
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
            have b11e52 : y = (M.op y y) ∨ x = (k x y) := by grind
            clear b11e51
            have b11e53 : x = (k x y) := by
              first
              | (have r₁ := b11e52
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e52 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e52
            have b11e76 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
              intro X0
              first
              | (have i₁ := b11e20 X0 y
                 have i₂ := b11e42 (σ X0)
                 grind)
              | exact superpose b11e42 b11e20
              | exact resolve b11e20 b11e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e42
            have b11e136 : (σ x) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b11e27
                 have i₂ := b11e76 x
                 grind)
              | exact superpose b11e76 b11e27
              | exact resolve b11e27 b11e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e27 b11e76
            have b11e146 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b11e136
                 have i₂ := b11e53
                 grind)
              | exact superpose b11e53 b11e136
              | exact resolve b11e136 b11e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e53 b11e136
            have b11e147 : False := by grind
            exact b11e147
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
          · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
            · have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e24 : x = (M.op x y) := by grind
              have b13e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : (σ (M.op x y)) ≠ (σ x) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e22
                | exact resolve b13e22 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e30 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b13e29
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e29
                | exact resolve b13e29 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e29
              have b13e31 : False := by grind
              exact b13e31
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
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
              intro X0 X1 X2
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : y ≠ (M.op y y) := by grind
            have b15e23 : x = (M.op x y) := by grind
            have b15e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b15e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            have b15e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X2) X2) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e14 (M.op (M.op X1 X0) X2) X2 X3
                 have i₂ := b15e14 X0 X1 X2
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e38 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e36 X0 X1 X2 x
                 have i₂ := b15e14 X1 X0 x
                 grind)
              | exact superpose b15e14 b15e36
              | exact resolve b15e36 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e36
            have b15e42 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k X0 x) := by
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
            have b15e43 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
              intro X0
              first
              | (have j0 := b15e42 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e42
            have b15e52 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
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
            have b15e56 : y = (M.op y y) ∨ x = (k x y) := by grind
            clear b15e52
            have b15e57 : x = (k x y) := by
              first
              | (have r₁ := b15e56
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e56 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e56
            have b15e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X1 X0
                 have i₂ := b15e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b15e19 b15e20
              | (have j1 := b15e19 (σ X0) (σ X0)
                 grind)
              | exact resolve b15e20 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e349 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e60 y x
                 grind)
              | exact superpose b15e60 b15e25
              | (have j1 := b15e60 y x
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e60 y x
                 grind)
              | exact resolve b15e25 b15e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e358 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b15e60 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e60
            have b15e359 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b15e358 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e358
            have b15e363 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b15e349
            have b15e372 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have r₁ := b15e363
                 have r₂ := b15e24
                 grind)
              | exact resolve b15e363 b15e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e363
            have b15e383 : (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b15e372
                 have i₂ := b15e57
                 grind)
              | exact superpose b15e57 b15e372
              | exact resolve b15e372 b15e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e57 b15e372
            have b15e384 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
              intro X0
              first
              | (have i₁ := b15e14 (σ x) (σ y) X0
                 have i₂ := b15e383
                 grind)
              | exact superpose b15e383 b15e14
              | exact resolve b15e14 b15e383
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e389 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) X0) := by
              intro X0
              first
              | (have i₁ := b15e38 (σ x) (σ y) x
                 have i₂ := b15e383
                 grind)
              | exact superpose b15e383 b15e38
              | exact resolve b15e38 b15e383
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e38 b15e383
            have b15e469 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 X1) (M.op (M.op X1 X0) (σ x))) := by
              intro X0 X1
              first
              | (have i₁ := b15e389 (M.op (M.op X1 X0) (σ x))
                 have i₂ := b15e14 X0 X1 (σ x)
                 grind)
              | exact superpose b15e14 b15e389
              | exact resolve b15e389 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e389
            have b15e2105 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e359 x
                 have i₂ := b15e43 x
                 grind)
              | exact superpose b15e43 b15e359
              | (have j0 := b15e359 x
                 grind)
              | exact resolve b15e359 b15e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e43 b15e359
            have b15e2116 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e2105
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e2105
              | exact resolve b15e2105 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2105
            have b15e2117 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b15e2116
            have b15e2176 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
              first
              | (have i₁ := b15e469 (σ x) (σ x)
                 have i₂ := b15e2117
                 grind)
              | exact superpose b15e2117 b15e469
              | exact resolve b15e469 b15e2117
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e469 b15e2117
            have b15e2179 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e2176
                 have i₂ := b15e384 (σ x)
                 grind)
              | exact superpose b15e384 b15e2176
              | exact resolve b15e2176 b15e384
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e384 b15e2176
            have b15e2192 : False := by grind
            exact b15e2192
          · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
                intro X0 X1 X2
                grind
              have b16e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b16e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b16e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b16e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e23 : y ≠ (M.op y y) := by grind
              have b16e24 : x = (M.op x y) := by grind
              have b16e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b16e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              have b16e27 : x ≠ (M.op x x) := by grind
              have b16e28 : y = (M.op y x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b16e21 (τ X0) X1
                   have i₂ := b16e17 X0
                   grind)
                | exact superpose b16e17 b16e21
                | exact resolve b16e21 b16e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X2) X2) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b16e15 (M.op (M.op X1 X0) X2) X2 X3
                   have i₂ := b16e15 X0 X1 X2
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e36 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e34 X0 X1 X2 x
                   have i₂ := b16e15 X1 X0 x
                   grind)
                | exact superpose b16e15 b16e34
                | exact resolve b16e34 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e34
              have b16e54 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
                first
                | (have i₁ := b16e19 x y
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e19
                | (have j0 := b16e19 x y
                   grind)
                | (have r₁ := b16e19 x y
                   have r₂ := b16e24
                   grind)
                | exact resolve b16e19 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e55 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
                first
                | (have i₁ := b16e19 y x
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e19
                | (have j0 := b16e19 y x
                   grind)
                | (have r₁ := b16e19 y x
                   have r₂ := b16e28
                   grind)
                | exact resolve b16e19 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e59 : x = (M.op x x) ∨ y = (k y x) := by grind
              clear b16e55
              have b16e60 : y = (M.op y y) ∨ x = (k x y) := by grind
              clear b16e54
              have b16e61 : y = (k y x) := by
                first
                | (have r₁ := b16e59
                   have r₂ := b16e27
                   grind)
                | exact resolve b16e59 b16e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e59
              have b16e62 : x = (k x y) := by
                first
                | (have r₁ := b16e60
                   have r₂ := b16e23
                   grind)
                | exact resolve b16e60 b16e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e60
              have b16e65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b16e21 X1 X0
                   have i₂ := b16e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b16e20 b16e21
                | (have j1 := b16e20 (σ X0) (σ X0)
                   grind)
                | exact resolve b16e21 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e18 X1 X0
                   have i₂ := b16e20 X2 X0
                   grind)
                | exact superpose b16e20 b16e18
                | (have j0 := b16e18 X1 X0
                   have j1 := b16e20 X2 X0
                   grind)
                | (have r₁ := b16e18 X0 X1
                   have r₂ := b16e20 X0 X1
                   grind)
                | (have r₁ := b16e18 X0 X1
                   have r₂ := b16e20 X1 X1
                   grind)
                | exact resolve b16e18 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e70 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b16e25
                   have i₂ := b16e20 X0 (σ y)
                   grind)
                | exact superpose b16e20 b16e25
                | (have j1 := b16e20 X0 (σ y)
                   grind)
                | (have r₁ := b16e25
                   have r₂ := b16e20 X0 (σ y)
                   grind)
                | (have r₁ := b16e25
                   have r₂ := b16e20 (σ y) (σ y)
                   grind)
                | exact resolve b16e25 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e71 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have j0 := b16e70 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e70
              have b16e72 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b16e67 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e67
              have b16e79 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b16e16 (k (τ X0) X1)
                   have i₂ := b16e30 X0 X1
                   grind)
                | exact superpose b16e30 b16e16
                | exact resolve b16e16 b16e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e30
              have b16e311 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X2 (σ X0)) = (k X2 (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e21 X1 X0
                   have i₂ := b16e72 (σ X0) X2 (σ X1)
                   grind)
                | exact superpose b16e72 b16e21
                | (have j1 := b16e72 (σ X0) X2 (σ X1)
                   grind)
                | exact resolve b16e21 b16e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e315 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b16e72 X1 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e72
              have b16e368 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b16e26
                   have i₂ := b16e65 y x
                   grind)
                | exact superpose b16e65 b16e26
                | (have j1 := b16e65 y x
                   grind)
                | (have r₁ := b16e26
                   have r₂ := b16e65 y x
                   grind)
                | exact resolve b16e26 b16e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e65
              have b16e382 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b16e368
              have b16e391 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have r₁ := b16e382
                   have r₂ := b16e25
                   grind)
                | exact resolve b16e382 b16e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e382
              have b16e402 : (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b16e391
                   have i₂ := b16e62
                   grind)
                | exact superpose b16e62 b16e391
                | exact resolve b16e391 b16e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e62 b16e391
              have b16e403 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
                intro X0
                first
                | (have i₁ := b16e15 (σ x) (σ y) X0
                   have i₂ := b16e402
                   grind)
                | exact superpose b16e402 b16e15
                | exact resolve b16e15 b16e402
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e408 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) X0) := by
                intro X0
                first
                | (have i₁ := b16e36 (σ x) (σ y) x
                   have i₂ := b16e402
                   grind)
                | exact superpose b16e402 b16e36
                | exact resolve b16e36 b16e402
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e36
              have b16e633 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b16e79 X0 y
                   have i₂ := b16e71 X0
                   grind)
                | exact superpose b16e71 b16e79
                | (have j1 := b16e71 X0
                   grind)
                | exact resolve b16e79 b16e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e71
              have b16e4145 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have j0 := b16e315 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e315
              have b16e4152 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b16e4145 X0
                   have j1 := b16e18 X0 X0
                   grind)
                | (have r₁ := b16e4145 x
                   have r₂ := b16e18 X0 x
                   grind)
                | exact resolve b16e4145 b16e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e4145
              have b16e30375 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
                first
                | (have i₁ := b16e633 (M.op (σ x) (σ y))
                   have i₂ := b16e403 (σ y)
                   grind)
                | exact superpose b16e403 b16e633
                | (have j0 := b16e633 (M.op (σ x) (σ y))
                   grind)
                | exact resolve b16e633 b16e403
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e403 b16e633
              have b16e30444 : (σ x) = (M.op (σ x) (σ y)) ∨ (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) := by
                first
                | (have i₁ := b16e30375
                   have i₂ := b16e408 (σ y)
                   grind)
                | exact superpose b16e408 b16e30375
                | exact resolve b16e30375 b16e408
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e408 b16e30375
              have b16e30476 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) := by
                first
                | (have r₁ := b16e30444
                   have r₂ := b16e26
                   grind)
                | exact resolve b16e30444 b16e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e30444
              have b16e30919 : ∀ X0 : G, (τ (σ (k y x))) = (k (τ (σ (k y x))) y) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                intro X0
                first
                | (have i₁ := b16e30476
                   have i₂ := b16e311 x y x
                   grind)
                | exact superpose b16e311 b16e30476
                | (have j1 := b16e311 x y X0
                   grind)
                | exact resolve b16e30476 b16e311
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e311 b16e30476
              have b16e30984 : ∀ X0 : G, (k y x) = (k (k y x) y) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                intro X0
                first
                | (have i₁ := b16e30919 X0
                   have i₂ := b16e16 (k y x)
                   grind)
                | exact superpose b16e16 b16e30919
                | (have j0 := b16e30919 X0
                   grind)
                | exact resolve b16e30919 b16e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e30919
              have b16e30994 : ∀ X0 : G, y = (k y y) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                intro X0
                first
                | (have i₁ := b16e30984 X0
                   have i₂ := b16e61
                   grind)
                | exact superpose b16e61 b16e30984
                | (have j0 := b16e30984 X0
                   grind)
                | exact resolve b16e30984 b16e61
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e30984
              have b16e31002 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                intro X0
                first
                | (have i₁ := b16e30994 X0
                   have i₂ := b16e4152 y
                   grind)
                | exact superpose b16e4152 b16e30994
                | (have j0 := b16e30994 X0
                   grind)
                | exact resolve b16e30994 b16e4152
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e4152 b16e30994
              have b16e31009 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                intro X0
                first
                | (have j0 := b16e31002 X0
                   grind)
                | (have r₁ := b16e31002 X0
                   have r₂ := b16e23
                   grind)
                | exact resolve b16e31002 b16e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e31002
              have b16e31012 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have i₁ := b16e31009 X0
                   have i₂ := b16e402
                   grind)
                | exact superpose b16e402 b16e31009
                | (have j0 := b16e31009 X0
                   grind)
                | exact resolve b16e31009 b16e402
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e31009
              have b16e33099 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ (σ x) = (σ y) := by
                intro X0
                first
                | (have i₁ := b16e79 X0 x
                   have i₂ := b16e31012 X0
                   grind)
                | exact superpose b16e31012 b16e79
                | exact resolve b16e79 b16e31012
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e79 b16e31012
              have b16e33958 : (τ (σ x)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b16e33099 (σ y)
                   have i₂ := b16e402
                   grind)
                | exact superpose b16e402 b16e33099
                | exact resolve b16e33099 b16e402
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e33099
              have b16e34016 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b16e33958
                   have i₂ := b16e16 y
                   grind)
                | exact superpose b16e16 b16e33958
                | exact resolve b16e33958 b16e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e33958
              have b16e34055 : x = (k y x) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b16e34016
                   have i₂ := b16e16 x
                   grind)
                | exact superpose b16e16 b16e34016
                | exact resolve b16e34016 b16e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e34016
              have b16e34075 : (σ x) = (σ y) ∨ x = y := by
                first
                | (have i₁ := b16e34055
                   have i₂ := b16e61
                   grind)
                | exact superpose b16e61 b16e34055
                | exact resolve b16e34055 b16e61
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e61 b16e34055
              have b16e35724 : x = (τ (σ y)) ∨ x = y := by
                first
                | (have i₁ := b16e16 x
                   have i₂ := b16e34075
                   grind)
                | exact superpose b16e34075 b16e16
                | exact resolve b16e16 b16e34075
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e34075
              have b16e35845 : x = y ∨ x = y := by
                first
                | (have i₁ := b16e35724
                   have i₂ := b16e16 y
                   grind)
                | exact superpose b16e16 b16e35724
                | exact resolve b16e35724 b16e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e35724
              have b16e35846 : x = y := by grind
              clear b16e35845
              have b16e35914 : (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b16e402
                   have i₂ := b16e35846
                   grind)
                | exact superpose b16e35846 b16e402
                | exact resolve b16e402 b16e35846
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e402 b16e35846
              have b16e35976 : False := by grind
              exact b16e35976
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
                intro X0 X1 X2
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : y ≠ (M.op y y) := by grind
              have b17e24 : x = (M.op x y) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b17e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              have b17e27 : x ≠ (M.op x x) := by grind
              have b17e28 : y ≠ (M.op y x) := by grind
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
              have b17e47 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
                first
                | (have i₁ := b17e19 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e19
                | (have j0 := b17e19 x y
                   grind)
                | (have r₁ := b17e19 x y
                   have r₂ := b17e24
                   grind)
                | exact resolve b17e19 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e51 : y = (M.op y y) ∨ x = (k x y) := by grind
              clear b17e47
              have b17e52 : x = (k x y) := by
                first
                | (have r₁ := b17e51
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e51 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e51
              have b17e55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 X1 X0
                   have i₂ := b17e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b17e20 b17e21
                | (have j1 := b17e20 (σ X0) (σ X0)
                   grind)
                | exact resolve b17e21 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e58 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X1 X1 X2
                   have i₂ := b17e20 X0 X1
                   grind)
                | exact superpose b17e20 b17e15
                | (have j1 := b17e20 X2 X0
                   grind)
                | exact resolve b17e15 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e69 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e30 X1 X0
                   have i₂ := b17e20 (τ X1) X0
                   grind)
                | exact superpose b17e20 b17e30
                | (have j1 := b17e20 X0 X0
                   grind)
                | exact resolve b17e30 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e30
              have b17e393 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e55 y x
                   grind)
                | exact superpose b17e55 b17e26
                | (have j1 := b17e55 y x
                   grind)
                | (have r₁ := b17e26
                   have r₂ := b17e55 y x
                   grind)
                | exact resolve b17e26 b17e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e55
              have b17e409 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b17e393
              have b17e419 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have r₁ := b17e409
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e409 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e409
              have b17e430 : (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b17e419
                   have i₂ := b17e52
                   grind)
                | exact superpose b17e52 b17e419
                | exact resolve b17e419 b17e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e52 b17e419
              have b17e431 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
                intro X0
                first
                | (have i₁ := b17e15 (σ x) (σ y) X0
                   have i₂ := b17e430
                   grind)
                | exact superpose b17e430 b17e15
                | exact resolve b17e15 b17e430
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e607 : ∀ X1 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) X1) = (k X1 (σ x)) ∨ (M.op X1 (σ x)) = X1 := by
                intro X1
                first
                | (have i₁ := b17e58 (σ x) x X1
                   have i₂ := b17e431 x
                   grind)
                | exact superpose b17e431 b17e58
                | (have j0 := b17e58 (σ x) X1 X1
                   grind)
                | exact resolve b17e58 b17e431
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e58 b17e431
              have b17e637 : ∀ X1 : G, (M.op (σ x) X1) = (k X1 (σ x)) ∨ (M.op X1 (σ x)) = X1 := by
                intro X1
                first
                | (have j0 := b17e607 X1
                   grind)
                | (have r₁ := b17e607 X1
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e607 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e607
              have b17e3852 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b17e69 X0 (σ X0)
                   have i₂ := b17e16 X0
                   grind)
                | exact superpose b17e16 b17e69
                | (have j0 := b17e69 X1 X1
                   grind)
                | exact resolve b17e69 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e69
              have b17e3940 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b17e3852 X0 X1
                   have i₂ := b17e21 X0 X1
                   grind)
                | exact superpose b17e21 b17e3852
                | (have j0 := b17e3852 X1 X1
                   grind)
                | exact resolve b17e3852 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3852
              have b17e7520 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
                intro X0
                first
                | (have i₁ := b17e21 X0 x
                   have i₂ := b17e637 (σ X0)
                   grind)
                | exact superpose b17e637 b17e21
                | (have j1 := b17e637 (σ X0)
                   grind)
                | exact resolve b17e21 b17e637
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e637
              have b17e57875 : (σ x) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e7520 y
                   grind)
                | exact superpose b17e7520 b17e26
                | (have j1 := b17e7520 y
                   grind)
                | exact resolve b17e26 b17e7520
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7520
              have b17e58296 : (σ x) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b17e57875
                   have i₂ := b17e430
                   grind)
                | exact superpose b17e430 b17e57875
                | exact resolve b17e57875 b17e430
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e57875
              have b17e58772 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b17e58296
                   have i₂ := b17e3940 y x
                   grind)
                | exact superpose b17e3940 b17e58296
                | (have j1 := b17e3940 x x
                   grind)
                | exact resolve b17e58296 b17e3940
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3940 b17e58296
              have b17e58773 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
                first
                | (have r₁ := b17e58772
                   have r₂ := b17e27
                   grind)
                | exact resolve b17e58772 b17e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e58772
              have b17e58778 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
                first
                | (have r₁ := b17e58773
                   have r₂ := b17e28
                   grind)
                | exact resolve b17e58773 b17e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e58773
              have b17e58786 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b17e58778
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e58778
                | exact resolve b17e58778 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e58778
              have b17e58787 : (σ x) = (σ y) := by grind
              clear b17e58786
              have b17e59278 : (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b17e430
                   have i₂ := b17e58787
                   grind)
                | exact superpose b17e58787 b17e430
                | exact resolve b17e430 b17e58787
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e430 b17e58787
              have b17e59468 : False := by grind
              exact b17e59468
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : y ≠ (M.op y y) := by grind
          have b18e23 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e44 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b18e45 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b18e44 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e44
          have b18e79 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e19 X0 y
               have i₂ := b18e45 (σ X0)
               grind)
            | exact superpose b18e45 b18e19
            | exact resolve b18e19 b18e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e45
          have b18e570 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b18e23
               have i₂ := b18e79 y
               grind)
            | exact superpose b18e79 b18e23
            | exact resolve b18e23 b18e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e79
          have b18e623 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b18e14 (k y y)
               have i₂ := b18e570
               grind)
            | exact superpose b18e570 b18e14
            | exact resolve b18e14 b18e570
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e570
          have b18e642 : y = (k y y) := by
            first
            | (have i₁ := b18e623
               have i₂ := b18e14 y
               grind)
            | exact superpose b18e14 b18e623
            | exact resolve b18e623 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e623
          have b18e769 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b18e18 y y
               have i₂ := b18e642
               grind)
            | exact superpose b18e642 b18e18
            | (have j0 := b18e18 y y
               grind)
            | exact resolve b18e18 b18e642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e642
          have b18e770 : y = (M.op y y) := by grind
          clear b18e769
          have b18e774 : False := by grind
          exact b18e774
        · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op y y) := by grind
            have b19e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e40 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b19e17 X0 (σ y)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e17
              | (have j0 := b19e17 X0 (σ y)
                 grind)
              | (have r₁ := b19e17 X0 (σ y)
                 have r₂ := b19e24
                 grind)
              | exact resolve b19e17 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e41 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have j0 := b19e40 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e40
            have b19e75 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
              intro X0
              first
              | (have i₁ := b19e20 X0 y
                 have i₂ := b19e41 (σ X0)
                 grind)
              | exact superpose b19e41 b19e20
              | exact resolve b19e20 b19e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e41
            have b19e134 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b19e24
                 have i₂ := b19e75 y
                 grind)
              | exact superpose b19e75 b19e24
              | exact resolve b19e24 b19e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e75
            have b19e243 : (k y y) = (τ (σ y)) := by
              first
              | (have i₁ := b19e15 (k y y)
                 have i₂ := b19e134
                 grind)
              | exact superpose b19e134 b19e15
              | exact resolve b19e15 b19e134
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e134
            have b19e245 : y = (k y y) := by
              first
              | (have i₁ := b19e243
                 have i₂ := b19e15 y
                 grind)
              | exact superpose b19e15 b19e243
              | exact resolve b19e243 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e243
            have b19e292 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e19 y y
                 have i₂ := b19e245
                 grind)
              | exact superpose b19e245 b19e19
              | (have j0 := b19e19 y y
                 grind)
              | exact resolve b19e19 b19e245
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e245
            have b19e293 : y = (M.op y y) := by grind
            clear b19e292
            have b19e295 : False := by grind
            exact b19e295
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op y y) := by grind
            have b20e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e40 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
            have b20e41 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have j0 := b20e40 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e40
            have b20e43 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
              intro X0
              first
              | (have i₁ := b20e20 X0 y
                 have i₂ := b20e41 (σ X0)
                 grind)
              | exact superpose b20e41 b20e20
              | exact resolve b20e20 b20e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e41
            have b20e82 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b20e24
                 have i₂ := b20e43 y
                 grind)
              | exact superpose b20e43 b20e24
              | exact resolve b20e24 b20e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e43
            have b20e110 : (k y y) = (τ (σ y)) := by
              first
              | (have i₁ := b20e15 (k y y)
                 have i₂ := b20e82
                 grind)
              | exact superpose b20e82 b20e15
              | exact resolve b20e15 b20e82
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e82
            have b20e112 : y = (k y y) := by
              first
              | (have i₁ := b20e110
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e110
              | exact resolve b20e110 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e110
            have b20e176 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b20e19 y y
                 have i₂ := b20e112
                 grind)
              | exact superpose b20e112 b20e19
              | (have j0 := b20e19 y y
                 grind)
              | exact resolve b20e19 b20e112
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e112
            have b20e177 : y = (M.op y y) := by grind
            clear b20e176
            have b20e179 : False := by grind
            exact b20e179
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
              intro X0 X1 X2
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : y ≠ (M.op y y) := by grind
            have b21e23 : x ≠ (M.op x y) := by grind
            have b21e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b21e25 : (σ x) = (M.op (σ x) (σ y)) := by grind
            have b21e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e30 : ∀ X0 : G, x = (M.op X0 (M.op x X0)) := by
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
            have b21e44 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b21e47 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b21e44
            have b21e48 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e47
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e47 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e47
            have b21e49 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e48
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e48
              | exact resolve b21e48 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e48
            have b21e52 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e49
                 grind)
              | exact superpose b21e49 b21e15
              | exact resolve b21e15 b21e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e49
            have b21e53 : x = (k x y) := by
              first
              | (have i₁ := b21e52
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e52
              | exact resolve b21e52 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e52
            have b21e72 : x = (M.op y x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e53
                 grind)
              | exact superpose b21e53 b21e19
              | (have j0 := b21e19 y y
                 grind)
              | exact resolve b21e19 b21e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e53
            have b21e73 : x = (M.op y x) ∨ x = (M.op x y) := by
              first
              | (have r₁ := b21e72
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e72 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e72
            have b21e75 : x = (M.op y x) := by
              first
              | (have r₁ := b21e73
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e73 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e73
            have b21e84 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
              intro X0
              first
              | (have i₁ := b21e14 x y X0
                 have i₂ := b21e75
                 grind)
              | exact superpose b21e75 b21e14
              | exact resolve b21e14 b21e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e75
            have b21e85 : x = (M.op x y) := by
              first
              | (have i₁ := b21e84 x
                 have i₂ := b21e30 x
                 grind)
              | exact superpose b21e30 b21e84
              | exact resolve b21e84 b21e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e30 b21e84
            have b21e86 : False := by grind
            exact b21e86
          · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : y ≠ (M.op y y) := by grind
              have b22e24 : x ≠ (M.op x y) := by grind
              have b22e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b22e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              have b22e28 : y = (M.op y x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e55 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
              have b22e58 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b22e55
              have b22e60 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e58
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e58 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e58
              have b22e61 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b22e60
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e60
                | exact resolve b22e60 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e60
              have b22e76 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e61
                   grind)
                | exact superpose b22e61 b22e16
                | exact resolve b22e16 b22e61
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e61
              have b22e77 : x = (k x y) := by
                first
                | (have i₁ := b22e76
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e76
                | exact resolve b22e76 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e76
              have b22e93 : x = (M.op y x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e77
                   grind)
                | exact superpose b22e77 b22e20
                | (have j0 := b22e20 y y
                   grind)
                | exact resolve b22e20 b22e77
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e77
              have b22e94 : x = (M.op y x) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b22e93
                   have r₂ := b22e23
                   grind)
                | exact resolve b22e93 b22e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e93
              have b22e96 : x = (M.op y x) := by
                first
                | (have r₁ := b22e94
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e94 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e94
              have b22e98 : x = y := by
                first
                | (have i₁ := b22e96
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e96
                | exact resolve b22e96 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e96
              have b22e118 : y = (M.op y y) := by
                first
                | (have i₁ := b22e28
                   have i₂ := b22e98
                   grind)
                | exact superpose b22e98 b22e28
                | exact resolve b22e28 b22e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e98
              have b22e123 : False := by grind
              exact b22e123
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b23e23 : y ≠ (M.op y y) := by grind
              have b23e24 : x ≠ (M.op x y) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b23e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              have b23e27 : x ≠ (M.op x x) := by grind
              have b23e28 : y ≠ (M.op y x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : (σ (M.op x y)) ≠ (σ x) := by
                first
                | (have i₁ := b23e22
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e22
                | exact resolve b23e22 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b23e21 (τ X0) X1
                   have i₂ := b23e17 X0
                   grind)
                | exact superpose b23e17 b23e21
                | exact resolve b23e21 b23e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b23e21 X1 (τ X0)
                   have i₂ := b23e17 X0
                   grind)
                | exact superpose b23e17 b23e21
                | exact resolve b23e21 b23e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b23e16 (k (τ X0) X1)
                   have i₂ := b23e30 X0 X1
                   grind)
                | exact superpose b23e30 b23e16
                | exact resolve b23e16 b23e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e36 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (M.op (σ x) X0)) := by
                intro X0
                first
                | (have i₁ := b23e15 (σ y) (σ x) X0
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e15
                | exact resolve b23e15 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X2) X2) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 (M.op (M.op X1 X0) X2) X2 X3
                   have i₂ := b23e15 X0 X1 X2
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e39 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e37 X0 X1 X2 x
                   have i₂ := b23e15 X1 X0 x
                   grind)
                | exact superpose b23e15 b23e37
                | exact resolve b23e37 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e37
              have b23e56 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
              have b23e58 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b23e56
              have b23e59 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e58
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e58 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e58
              have b23e60 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b23e59
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e59
                | exact resolve b23e59 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e59
              have b23e64 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e60
                   grind)
                | exact superpose b23e60 b23e16
                | exact resolve b23e16 b23e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e60
              have b23e65 : x = (k x y) := by
                first
                | (have i₁ := b23e64
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e64
                | exact resolve b23e64 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e64
              have b23e72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b23e21 X1 X0
                   have i₂ := b23e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b23e20 b23e21
                | (have j1 := b23e20 (σ X0) (σ X0)
                   grind)
                | exact resolve b23e21 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e75 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e18 X1 X0
                   have i₂ := b23e20 X2 X0
                   grind)
                | exact superpose b23e20 b23e18
                | (have j0 := b23e18 X1 X0
                   have j1 := b23e20 X2 X0
                   grind)
                | (have r₁ := b23e18 X0 X1
                   have r₂ := b23e20 X0 X1
                   grind)
                | (have r₁ := b23e18 X0 X1
                   have r₂ := b23e20 X1 X1
                   grind)
                | exact resolve b23e18 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e76 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e15 X1 X1 X2
                   have i₂ := b23e20 X0 X1
                   grind)
                | exact superpose b23e20 b23e15
                | (have j1 := b23e20 X2 X0
                   grind)
                | exact resolve b23e15 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e80 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b23e75 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e75
              have b23e84 : x = (M.op y x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e65
                   grind)
                | exact superpose b23e65 b23e20
                | (have j0 := b23e20 y y
                   grind)
                | exact resolve b23e20 b23e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e65
              have b23e85 : x = (M.op y x) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b23e84
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e84 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e84
              have b23e87 : x = (M.op y x) := by
                first
                | (have r₁ := b23e85
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e85 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e85
              have b23e89 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) X0) := by
                intro X0
                first
                | (have i₁ := b23e39 (σ y) (σ x) x
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e39
                | exact resolve b23e39 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e93 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 X1) (M.op (M.op X1 X0) (M.op X2 X3))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e39 X3 X2 (M.op (M.op X1 X0) (M.op X2 X3))
                   have i₂ := b23e15 X0 X1 (M.op X2 X3)
                   grind)
                | exact superpose b23e15 b23e39
                | exact resolve b23e39 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e98 : x ≠ y := by
                first
                | (have i₁ := b23e28
                   have i₂ := b23e87
                   grind)
                | exact superpose b23e87 b23e28
                | exact resolve b23e28 b23e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e99 : ∀ X0 : G, x = (M.op (M.op x X0) X0) := by
                intro X0
                first
                | (have i₁ := b23e39 x y x
                   have i₂ := b23e87
                   grind)
                | exact superpose b23e87 b23e39
                | exact resolve b23e39 b23e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e101 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
                intro X0
                first
                | (have i₁ := b23e15 x y X0
                   have i₂ := b23e87
                   grind)
                | exact superpose b23e87 b23e15
                | exact resolve b23e15 b23e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e87
              have b23e210 : ∀ X1 : G, (M.op (σ x) X1) = (k X1 (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op X1 (σ x)) = X1 := by
                intro X1
                first
                | (have i₁ := b23e36 x
                   have i₂ := b23e76 (σ x) x X1
                   grind)
                | exact superpose b23e76 b23e36
                | (have j1 := b23e76 (σ x) X1 X1
                   grind)
                | exact resolve b23e36 b23e76
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e260 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) X2) = (k X2 (σ X1)) ∨ (M.op X2 (σ X1)) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e21 X0 X1
                   have i₂ := b23e80 (σ X1) (σ X0) X2
                   grind)
                | exact superpose b23e80 b23e21
                | (have j1 := b23e80 (σ X1) X1 X2
                   grind)
                | exact resolve b23e21 b23e80
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e270 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b23e80 X1 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e80
              have b23e280 : ∀ X1 : G, x = (M.op x y) ∨ (M.op x X1) = (k X1 x) ∨ (M.op X1 x) = X1 := by
                intro X1
                first
                | (have i₁ := b23e76 x x X1
                   have i₂ := b23e101 x
                   grind)
                | exact superpose b23e101 b23e76
                | (have j0 := b23e76 x X1 X1
                   grind)
                | exact resolve b23e76 b23e101
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e76
              have b23e292 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op x (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b23e39 X1 X0 (M.op x (M.op X0 X1))
                   have i₂ := b23e101 (M.op X0 X1)
                   grind)
                | exact superpose b23e101 b23e39
                | exact resolve b23e39 b23e101
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e39
              have b23e301 : ∀ X1 : G, (M.op x X1) = (k X1 x) ∨ (M.op X1 x) = X1 := by
                intro X1
                first
                | (have j0 := b23e280 X1
                   grind)
                | (have r₁ := b23e280 X1
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e280 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e280
              have b23e366 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b23e19 (σ X0) (σ X1)
                   have i₂ := b23e72 X1 X0
                   grind)
                | exact superpose b23e72 b23e19
                | (have j0 := b23e19 (σ X0) (σ X1)
                   have j1 := b23e72 X1 X0
                   grind)
                | (have r₁ := b23e19 (σ X0) (σ X0)
                   have r₂ := b23e72 X0 X1
                   grind)
                | (have r₁ := b23e19 (σ X1) (σ X0)
                   have r₂ := b23e72 X0 X1
                   grind)
                | exact resolve b23e19 b23e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e72
              have b23e376 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have j0 := b23e366 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e366
              have b23e377 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have j0 := b23e376 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e376
              have b23e385 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b23e377 X0 X1
                   have i₂ := b23e21 X0 X1
                   grind)
                | exact superpose b23e21 b23e377
                | (have j0 := b23e377 X0 X1
                   grind)
                | exact resolve b23e377 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e377
              have b23e802 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) ∨ (τ X0) = (M.op (τ X0) x) := by
                intro X0
                first
                | (have i₁ := b23e30 X0 x
                   have i₂ := b23e301 (τ X0)
                   grind)
                | exact superpose b23e301 b23e30
                | (have j1 := b23e301 (τ X0)
                   grind)
                | exact resolve b23e30 b23e301
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e301
              have b23e1108 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op X1 X0) (M.op (σ y) (σ x))) := by
                intro X0 X1
                first
                | (have i₁ := b23e93 X1 X0 (σ x) (M.op X0 X1)
                   have i₂ := b23e36 (M.op X0 X1)
                   grind)
                | exact superpose b23e36 b23e93
                | exact resolve b23e93 b23e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e93
              have b23e3767 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b23e270 (σ y) (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e270
                | (have j0 := b23e270 (σ y) (σ x)
                   grind)
                | exact resolve b23e270 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e3772 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have j0 := b23e270 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e270
              have b23e3777 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b23e3772 X0
                   have j1 := b23e18 X0 X0
                   grind)
                | (have r₁ := b23e3772 x
                   have r₂ := b23e18 X0 x
                   grind)
                | exact resolve b23e3772 b23e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3772
              have b23e3780 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b23e3767
                   have i₂ := b23e21 y x
                   grind)
                | exact superpose b23e21 b23e3767
                | exact resolve b23e3767 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3767
              have b23e3861 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                first
                | (have i₁ := b23e21 X0 X0
                   have i₂ := b23e3777 (σ X0)
                   grind)
                | exact superpose b23e3777 b23e21
                | exact resolve b23e21 b23e3777
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e3872 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b23e3861 X0
                   have i₂ := b23e3777 X0
                   grind)
                | exact superpose b23e3777 b23e3861
                | exact resolve b23e3861 b23e3777
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3777 b23e3861
              have b23e4133 : (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
                first
                | (have i₁ := b23e89 (σ x)
                   have i₂ := b23e3872 x
                   grind)
                | exact superpose b23e3872 b23e89
                | exact resolve b23e89 b23e3872
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e89
              have b23e4134 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (M.op x x))) := by
                first
                | (have i₁ := b23e36 (σ x)
                   have i₂ := b23e3872 x
                   grind)
                | exact superpose b23e3872 b23e36
                | exact resolve b23e36 b23e3872
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e36
              have b23e4980 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                intro X0
                first
                | (have i₁ := b23e21 X0 x
                   have i₂ := b23e210 (σ X0)
                   grind)
                | exact superpose b23e210 b23e21
                | (have j1 := b23e210 (σ X0)
                   grind)
                | exact resolve b23e21 b23e210
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e210
              have b23e9149 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e21 X1 X0
                   have i₂ := b23e260 X2 X0 (σ X1)
                   grind)
                | exact superpose b23e260 b23e21
                | (have j1 := b23e260 X2 X0 (σ X1)
                   grind)
                | exact resolve b23e21 b23e260
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e260
              have b23e9736 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (k X1 (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b23e385 X0 (τ X0)
                   have i₂ := b23e17 X0
                   grind)
                | exact superpose b23e17 b23e385
                | (have j0 := b23e385 X1 (τ X0)
                   grind)
                | exact resolve b23e385 b23e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e385
              have b23e9982 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (σ (k X1 (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b23e9736 X0 X1
                   have i₂ := b23e31 X0 X1
                   grind)
                | exact superpose b23e31 b23e9736
                | (have j0 := b23e9736 X0 X1
                   grind)
                | exact resolve b23e9736 b23e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e9736
              have b23e10029 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b23e9982 X0 X1
                   have i₂ := b23e31 X0 X1
                   grind)
                | exact superpose b23e31 b23e9982
                | (have j0 := b23e9982 X0 X1
                   grind)
                | exact resolve b23e9982 b23e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e31 b23e9982
              have b23e41660 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e802 (σ X0)
                   have i₂ := b23e16 X0
                   grind)
                | exact superpose b23e16 b23e802
                | exact resolve b23e802 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e802
              have b23e41789 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e41660 X0
                   have i₂ := b23e21 X0 x
                   grind)
                | exact superpose b23e21 b23e41660
                | (have j0 := b23e41660 X0
                   grind)
                | exact resolve b23e41660 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e41660
              have b23e72110 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b23e10029 X0 (τ X0)
                   have i₂ := b23e17 X0
                   grind)
                | exact superpose b23e17 b23e10029
                | (have j0 := b23e10029 X1 X1
                   grind)
                | exact resolve b23e10029 b23e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e10029
              have b23e72798 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (k X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e15 X1 X1 X2
                   have i₂ := b23e72110 X0 X1
                   grind)
                | exact superpose b23e72110 b23e15
                | (have j1 := b23e72110 X2 X0
                   grind)
                | exact resolve b23e15 b23e72110
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e72110
              have b23e114734 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 x) = (M.op x X0) ∨ (k X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e292 x y
                   have i₂ := b23e72798 x (M.op x y) X0
                   grind)
                | exact superpose b23e72798 b23e292
                | (have j1 := b23e72798 x x X0
                   grind)
                | exact resolve b23e292 b23e72798
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e292 b23e72798
              have b23e114836 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (k X0 x) = X0 := by
                intro X0
                first
                | (have j0 := b23e114734 X0
                   grind)
                | (have r₁ := b23e114734 X0
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e114734 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e114734
              have b23e114905 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) ∨ (τ X0) = (k (τ X0) x) := by
                intro X0
                first
                | (have i₁ := b23e30 X0 x
                   have i₂ := b23e114836 (τ X0)
                   grind)
                | exact superpose b23e114836 b23e30
                | (have j1 := b23e114836 (τ X0)
                   grind)
                | exact resolve b23e30 b23e114836
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e114836
              have b23e115518 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (k X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e114905 (σ X0)
                   have i₂ := b23e16 X0
                   grind)
                | exact superpose b23e16 b23e114905
                | exact resolve b23e114905 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e114905
              have b23e115553 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (k X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e115518 X0
                   have i₂ := b23e21 X0 x
                   grind)
                | exact superpose b23e21 b23e115518
                | (have j0 := b23e115518 X0
                   grind)
                | exact resolve b23e115518 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e115518
              have b23e117568 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b23e26
                   have i₂ := b23e4980 y
                   grind)
                | exact superpose b23e4980 b23e26
                | (have j1 := b23e4980 y
                   grind)
                | exact resolve b23e26 b23e4980
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e4980
              have b23e117585 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have r₁ := b23e117568
                   have r₂ := b23e3780
                   grind)
                | exact resolve b23e117568 b23e3780
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3780 b23e117568
              have b23e117685 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b23e1108 (σ x) (σ y)
                   have i₂ := b23e117585
                   grind)
                | exact superpose b23e117585 b23e1108
                | exact resolve b23e1108 b23e117585
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1108 b23e117585
              have b23e117733 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b23e117685
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e117685
                | exact resolve b23e117685 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e117685
              have b23e117776 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b23e117733
                   have i₂ := b23e3872 x
                   grind)
                | exact superpose b23e3872 b23e117733
                | exact resolve b23e117733 b23e3872
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e117733
              have b23e117791 : (σ x) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b23e117776
                   have i₂ := b23e3872 y
                   grind)
                | exact superpose b23e3872 b23e117776
                | exact resolve b23e117776 b23e3872
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3872 b23e117776
              have b23e118250 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b23e41789 y
                   have i₂ := b23e117791
                   grind)
                | exact superpose b23e117791 b23e41789
                | (have j0 := b23e41789 y
                   grind)
                | exact resolve b23e41789 b23e117791
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e117791
              have b23e118315 : y = (M.op y x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
                first
                | (have r₁ := b23e118250
                   have r₂ := b23e29
                   grind)
                | exact resolve b23e118250 b23e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e118250
              have b23e118328 : (σ (M.op x x)) = (σ (M.op y y)) := by
                first
                | (have r₁ := b23e118315
                   have r₂ := b23e28
                   grind)
                | exact resolve b23e118315 b23e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e118315
              have b23e118384 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (M.op y y))) := by
                first
                | (have i₁ := b23e4134
                   have i₂ := b23e118328
                   grind)
                | exact superpose b23e118328 b23e4134
                | exact resolve b23e4134 b23e118328
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e4134
              have b23e118385 : (σ x) = (M.op (σ (M.op y y)) (σ x)) := by
                first
                | (have i₁ := b23e4133
                   have i₂ := b23e118328
                   grind)
                | exact superpose b23e118328 b23e4133
                | exact resolve b23e4133 b23e118328
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e4133
              have b23e118415 : (M.op x x) = (τ (σ (M.op y y))) := by
                first
                | (have i₁ := b23e16 (M.op x x)
                   have i₂ := b23e118328
                   grind)
                | exact superpose b23e118328 b23e16
                | exact resolve b23e16 b23e118328
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e118416 : ∀ X0 : G, (σ (k (M.op x x) X0)) = (k (σ (M.op y y)) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b23e21 (M.op x x) X0
                   have i₂ := b23e118328
                   grind)
                | exact superpose b23e118328 b23e21
                | exact resolve b23e21 b23e118328
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e118328
              have b23e118480 : ∀ X0 : G, (σ (k (M.op x x) X0)) = (σ (k (M.op y y) X0)) := by
                intro X0
                first
                | (have i₁ := b23e118416 X0
                   have i₂ := b23e21 (M.op y y) X0
                   grind)
                | exact superpose b23e21 b23e118416
                | exact resolve b23e118416 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e118416
              have b23e118481 : (M.op y y) = (M.op x x) := by
                first
                | (have i₁ := b23e118415
                   have i₂ := b23e16 (M.op y y)
                   grind)
                | exact superpose b23e16 b23e118415
                | exact resolve b23e118415 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e118415
              have b23e118570 : x ≠ (M.op y y) := by
                first
                | (have i₁ := b23e27
                   have i₂ := b23e118481
                   grind)
                | exact superpose b23e118481 b23e27
                | exact resolve b23e27 b23e118481
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e118481
              have b23e120584 : (σ (k (M.op y y) x)) = (σ (M.op x (M.op x x))) ∨ (M.op x x) = (M.op (M.op x x) x) := by
                first
                | (have i₁ := b23e41789 (M.op x x)
                   have i₂ := b23e118480 x
                   grind)
                | exact superpose b23e118480 b23e41789
                | (have j0 := b23e41789 (M.op x x)
                   grind)
                | exact resolve b23e41789 b23e118480
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e41789 b23e118480
              have b23e120653 : (σ (M.op x y)) = (σ (k (M.op y y) x)) ∨ (M.op x x) = (M.op (M.op x x) x) := by
                first
                | (have i₁ := b23e120584
                   have i₂ := b23e101 x
                   grind)
                | exact superpose b23e101 b23e120584
                | exact resolve b23e120584 b23e101
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e101 b23e120584
              have b23e120727 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ (k (M.op y y) x)) := by
                first
                | (have i₁ := b23e120653
                   have i₂ := b23e99 x
                   grind)
                | exact superpose b23e99 b23e120653
                | exact resolve b23e120653 b23e99
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e120653
              have b23e120765 : (σ (M.op x y)) = (σ (k (M.op y y) x)) := by
                first
                | (have r₁ := b23e120727
                   have r₂ := b23e27
                   grind)
                | exact resolve b23e120727 b23e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e120727
              have b23e120836 : (k (M.op y y) x) = (τ (σ (M.op x y))) := by
                first
                | (have i₁ := b23e16 (k (M.op y y) x)
                   have i₂ := b23e120765
                   grind)
                | exact superpose b23e120765 b23e16
                | exact resolve b23e16 b23e120765
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e120895 : (M.op x y) = (k (M.op y y) x) := by
                first
                | (have i₁ := b23e120836
                   have i₂ := b23e16 (M.op x y)
                   grind)
                | exact superpose b23e16 b23e120836
                | exact resolve b23e120836 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e120836
              have b23e131361 : ∀ X0 : G, (σ x) = (σ (k (M.op y y) x)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
                intro X0
                first
                | (have i₁ := b23e118385
                   have i₂ := b23e9149 x X0 (M.op y y)
                   grind)
                | exact superpose b23e9149 b23e118385
                | (have j1 := b23e9149 x X0 x
                   grind)
                | exact resolve b23e118385 b23e9149
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e9149
              have b23e131375 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
                intro X0
                first
                | (have i₁ := b23e131361 X0
                   have i₂ := b23e120765
                   grind)
                | exact superpose b23e120765 b23e131361
                | (have j0 := b23e131361 X0
                   grind)
                | exact resolve b23e131361 b23e120765
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e120765 b23e131361
              have b23e131385 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
                intro X0
                first
                | (have j0 := b23e131375 X0
                   grind)
                | (have r₁ := b23e131375 X0
                   have r₂ := b23e29
                   grind)
                | exact resolve b23e131375 b23e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e131375
              have b23e131403 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (M.op (σ x) X0) = (σ (k (τ X0) x)) := by
                intro X0
                first
                | (have i₁ := b23e131385 (τ X0)
                   have i₂ := b23e17 X0
                   grind)
                | exact superpose b23e17 b23e131385
                | exact resolve b23e131385 b23e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e131385
              have b23e131642 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e131403 X0
                   have i₂ := b23e30 X0 x
                   grind)
                | exact superpose b23e30 b23e131403
                | (have j0 := b23e131403 X0
                   grind)
                | exact resolve b23e131403 b23e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e30 b23e131403
              have b23e131748 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op (σ x) X0)) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e35 X0 x
                   have i₂ := b23e131642 X0
                   grind)
                | exact superpose b23e131642 b23e35
                | (have j1 := b23e131642 X0
                   grind)
                | exact resolve b23e35 b23e131642
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e35 b23e131642
              have b23e131802 : (τ (M.op (σ y) (σ x))) = (k (τ (σ (M.op y y))) x) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ x)) := by
                first
                | (have i₁ := b23e131748 (σ (M.op y y))
                   have i₂ := b23e118384
                   grind)
                | exact superpose b23e118384 b23e131748
                | (have j0 := b23e131748 (σ (M.op y y))
                   grind)
                | exact resolve b23e131748 b23e118384
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e118384
              have b23e131803 : (τ (σ x)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b23e131748 (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e131748
                | (have j0 := b23e131748 (σ y)
                   grind)
                | exact resolve b23e131748 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e131748
              have b23e131884 : (τ (σ x)) = (k y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b23e131803
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e131803
                | exact resolve b23e131803 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e131803
              have b23e131885 : (τ (M.op (σ y) (σ x))) = (k (M.op y y) x) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ x)) := by
                first
                | (have i₁ := b23e131802
                   have i₂ := b23e16 (M.op y y)
                   grind)
                | exact superpose b23e16 b23e131802
                | exact resolve b23e131802 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e131802
              have b23e131914 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y x) := by
                first
                | (have i₁ := b23e131884
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e131884
                | exact resolve b23e131884 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e131884
              have b23e131915 : (M.op x y) = (τ (M.op (σ y) (σ x))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ x)) := by
                first
                | (have i₁ := b23e131885
                   have i₂ := b23e120895
                   grind)
                | exact superpose b23e120895 b23e131885
                | exact resolve b23e131885 b23e120895
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e120895 b23e131885
              have b23e131920 : (M.op x y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (σ (M.op y y)) := by
                first
                | (have i₁ := b23e131915
                   have i₂ := b23e118385
                   grind)
                | exact superpose b23e118385 b23e131915
                | exact resolve b23e131915 b23e118385
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e118385 b23e131915
              have b23e134593 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k y x) := by
                first
                | (have i₁ := b23e131920
                   have i₂ := b23e131914
                   grind)
                | exact superpose b23e131914 b23e131920
                | exact resolve b23e131920 b23e131914
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e131914 b23e131920
              have b23e134627 : (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
                first
                | (have i₁ := b23e134593
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e134593
                | exact resolve b23e134593 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e134593
              have b23e134689 : (M.op y y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
                first
                | (have i₁ := b23e16 (M.op y y)
                   have i₂ := b23e134627
                   grind)
                | exact superpose b23e134627 b23e16
                | exact resolve b23e16 b23e134627
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e134627
              have b23e134740 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (k y x) := by
                first
                | (have i₁ := b23e134689
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e134689
                | exact resolve b23e134689 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e134689
              have b23e134758 : x = (k y x) ∨ y = (M.op x y) := by
                first
                | (have r₁ := b23e134740
                   have r₂ := b23e118570
                   grind)
                | exact resolve b23e134740 b23e118570
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e134740
              have b23e134810 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
                first
                | (have i₁ := b23e115553 y
                   have i₂ := b23e134758
                   grind)
                | exact superpose b23e134758 b23e115553
                | exact resolve b23e115553 b23e134758
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e115553 b23e134758
              have b23e134850 : x = y ∨ y = (M.op x y) := by
                first
                | (have r₁ := b23e134810
                   have r₂ := b23e29
                   grind)
                | exact resolve b23e134810 b23e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e29 b23e134810
              have b23e134889 : y = (M.op x y) := by
                first
                | (have r₁ := b23e134850
                   have r₂ := b23e98
                   grind)
                | exact resolve b23e134850 b23e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e98 b23e134850
              have b23e134970 : x = (M.op y y) := by
                first
                | (have i₁ := b23e99 y
                   have i₂ := b23e134889
                   grind)
                | exact superpose b23e134889 b23e99
                | exact resolve b23e99 b23e134889
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e99 b23e134889
              have b23e135267 : False := by grind
              exact b23e135267
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
              intro X0 X1 X2
              grind
            have b24e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b24e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : y ≠ (M.op y y) := by grind
            have b24e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b24e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
            have b24e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 (τ X0)
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e29 : ∀ X0 : G, x = (M.op X0 (M.op x X0)) := by
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
            have b24e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X2) X2) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 (M.op (M.op X1 X0) X2) X2 X3
                 have i₂ := b24e14 X0 X1 X2
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X0) (M.op X3 X2)) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X2 X3 (M.op (M.op X1 X0) (M.op X3 X2))
                 have i₂ := b24e14 X0 X1 (M.op X3 X2)
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e32 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e30 X0 X1 X2 x
                 have i₂ := b24e14 X1 X0 x
                 grind)
              | exact superpose b24e14 b24e30
              | exact resolve b24e30 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e30
            have b24e36 : ∀ X0 X1 : G, (M.op (M.op x X0) X0) = (M.op X1 (M.op x X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 (M.op x X0) X0 X1
                 have i₂ := b24e29 X0
                 grind)
              | exact superpose b24e29 b24e14
              | exact resolve b24e14 b24e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e37 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x (M.op X1 X0)) x) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X0 X1 (M.op x (M.op X1 X0))
                 have i₂ := b24e29 (M.op X1 X0)
                 grind)
              | exact superpose b24e29 b24e14
              | exact resolve b24e14 b24e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e38 : ∀ X0 : G, x = (M.op (M.op x X0) X0) := by
              intro X0
              first
              | (have i₁ := b24e36 X0 x
                 have i₂ := b24e29 x
                 grind)
              | exact superpose b24e29 b24e36
              | exact resolve b24e36 b24e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e36
            have b24e40 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k X0 x) := by
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
            have b24e41 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
              intro X0
              first
              | (have j0 := b24e40 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e40
            have b24e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 X0
                 have i₂ := b24e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b24e19 b24e20
              | (have j1 := b24e19 (σ X0) (σ X0)
                 grind)
              | exact resolve b24e20 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e57 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b24e24
                 have i₂ := b24e19 X0 (σ y)
                 grind)
              | exact superpose b24e19 b24e24
              | (have j1 := b24e19 X0 (σ y)
                 grind)
              | (have r₁ := b24e24
                 have r₂ := b24e19 X0 (σ y)
                 grind)
              | (have r₁ := b24e24
                 have r₂ := b24e19 (σ y) (σ y)
                 grind)
              | exact resolve b24e24 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e58 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b24e57 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e57
            have b24e65 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b24e15 (k (τ X0) X1)
                 have i₂ := b24e27 X0 X1
                 grind)
              | exact superpose b24e27 b24e15
              | exact resolve b24e15 b24e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e27
            have b24e125 : ∀ X0 X1 : G, (M.op x (M.op X1 X0)) = (M.op (M.op X0 X1) x) := by
              intro X0 X1
              first
              | (have i₁ := b24e31 X1 X0 (M.op X0 X1) x
                 have i₂ := b24e29 (M.op X0 X1)
                 grind)
              | exact superpose b24e29 b24e31
              | exact resolve b24e31 b24e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e29 b24e31
            have b24e179 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b24e65 X0 y
                 have i₂ := b24e58 X0
                 grind)
              | exact superpose b24e58 b24e65
              | (have j1 := b24e58 X0
                 grind)
              | exact resolve b24e65 b24e58
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e58
            have b24e371 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e18 (σ X0) (σ X1)
                 have i₂ := b24e52 X1 X0
                 grind)
              | exact superpose b24e52 b24e18
              | (have j0 := b24e18 (σ X0) (σ X1)
                 have j1 := b24e52 X1 X0
                 grind)
              | (have r₁ := b24e18 (σ X0) (σ X0)
                 have r₂ := b24e52 X0 X1
                 grind)
              | (have r₁ := b24e18 (σ X1) (σ X0)
                 have r₂ := b24e52 X0 X1
                 grind)
              | exact resolve b24e18 b24e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e380 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b24e52 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e52
            have b24e381 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b24e380 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e380
            have b24e383 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have j0 := b24e371 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e371
            have b24e384 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have j0 := b24e383 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e383
            have b24e394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e384 X0 X1
                 have i₂ := b24e20 X0 X1
                 grind)
              | exact superpose b24e20 b24e384
              | (have j0 := b24e384 X0 X1
                 grind)
              | exact resolve b24e384 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e384
            have b24e1707 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b24e381 x
                 have i₂ := b24e41 x
                 grind)
              | exact superpose b24e41 b24e381
              | (have j0 := b24e381 x
                 grind)
              | exact resolve b24e381 b24e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e381
            have b24e1716 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b24e1707
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e1707
              | exact resolve b24e1707 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1707
            have b24e1717 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b24e1716
            have b24e1724 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b24e17 X0 (σ x)
                 have i₂ := b24e1717
                 grind)
              | exact superpose b24e1717 b24e17
              | (have j0 := b24e17 X0 (σ x)
                 grind)
              | (have r₁ := b24e17 X0 (σ x)
                 have r₂ := b24e1717
                 grind)
              | exact resolve b24e17 b24e1717
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1725 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) X0)) := by
              intro X0
              first
              | (have i₁ := b24e14 (σ x) (σ x) x
                 have i₂ := b24e1717
                 grind)
              | exact superpose b24e1717 b24e14
              | exact resolve b24e14 b24e1717
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1729 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) X0) := by
              intro X0
              first
              | (have i₁ := b24e32 (σ x) (σ x) x
                 have i₂ := b24e1717
                 grind)
              | exact superpose b24e1717 b24e32
              | exact resolve b24e32 b24e1717
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1717
            have b24e1748 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have j0 := b24e1724 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1724
            have b24e2579 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) := by
              intro X0
              first
              | (have i₁ := b24e65 X0 x
                 have i₂ := b24e1748 X0
                 grind)
              | exact superpose b24e1748 b24e65
              | exact resolve b24e65 b24e1748
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e65 b24e1748
            have b24e2601 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 (σ x))) := by
              intro X0
              first
              | (have i₁ := b24e2579 X0
                 have i₂ := b24e41 (τ X0)
                 grind)
              | exact superpose b24e41 b24e2579
              | exact resolve b24e2579 b24e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e41 b24e2579
            have b24e4610 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op (M.op X0 X1) (σ x))) x) := by
              intro X0 X1
              first
              | (have i₁ := b24e2601 (M.op (M.op X0 X1) (σ x))
                 have i₂ := b24e32 X1 X0 (σ x)
                 grind)
              | exact superpose b24e32 b24e2601
              | exact resolve b24e2601 b24e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e4649 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (M.op (τ (M.op X0 X1)) x) x) := by
              intro X0 X1
              first
              | (have i₁ := b24e4610 X0 X1
                 have i₂ := b24e2601 (M.op X0 X1)
                 grind)
              | exact superpose b24e2601 b24e4610
              | exact resolve b24e4610 b24e2601
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2601 b24e4610
            have b24e4663 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op x (M.op x (τ (M.op X0 X1)))) := by
              intro X0 X1
              first
              | (have i₁ := b24e4649 X0 X1
                 have i₂ := b24e125 (τ (M.op X0 X1)) x
                 grind)
              | exact superpose b24e125 b24e4649
              | exact resolve b24e4649 b24e125
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e125 b24e4649
            have b24e5955 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (k X1 (τ X0))) := by
              intro X0 X1
              first
              | (have i₁ := b24e394 X0 (τ X0)
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e394
              | (have j0 := b24e394 X1 (τ X0)
                 grind)
              | exact resolve b24e394 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e394
            have b24e6134 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (σ (k X1 (τ X0))) := by
              intro X0 X1
              first
              | (have i₁ := b24e5955 X0 X1
                 have i₂ := b24e28 X0 X1
                 grind)
              | exact superpose b24e28 b24e5955
              | (have j0 := b24e5955 X0 X1
                 grind)
              | exact resolve b24e5955 b24e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e5955
            have b24e6177 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e6134 X0 X1
                 have i₂ := b24e28 X0 X1
                 grind)
              | exact superpose b24e28 b24e6134
              | (have j0 := b24e6134 X0 X1
                 grind)
              | exact resolve b24e6134 b24e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e28 b24e6134
            have b24e36097 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op (M.op (τ (M.op X0 X1)) X2) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e32 (M.op x (τ (M.op X0 X1))) x X2
                 have i₂ := b24e4663 X0 X1
                 grind)
              | exact superpose b24e4663 b24e32
              | exact resolve b24e32 b24e4663
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32 b24e4663
            have b24e39252 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) y) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
              first
              | (have i₁ := b24e179 (M.op (σ x) (σ y))
                 have i₂ := b24e1725 (σ y)
                 grind)
              | exact superpose b24e1725 b24e179
              | (have j0 := b24e179 (M.op (σ x) (σ y))
                 grind)
              | exact resolve b24e179 b24e1725
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e179 b24e1725
            have b24e39315 : x = (k (τ (M.op (σ x) (σ y))) y) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
              first
              | (have i₁ := b24e39252
                 have i₂ := b24e15 x
                 grind)
              | exact superpose b24e15 b24e39252
              | exact resolve b24e39252 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e39252
            have b24e39345 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (τ (M.op (σ x) (σ y))) y) := by
              first
              | (have i₁ := b24e39315
                 have i₂ := b24e1729 (σ y)
                 grind)
              | exact superpose b24e1729 b24e39315
              | exact resolve b24e39315 b24e1729
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1729 b24e39315
            have b24e39365 : x = (k (τ (M.op (σ x) (σ y))) y) := by
              first
              | (have r₁ := b24e39345
                 have r₂ := b24e25
                 grind)
              | exact resolve b24e39345 b24e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e39345
            have b24e84622 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e6177 X0 (τ X0)
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e6177
              | (have j0 := b24e6177 X1 X1
                 grind)
              | exact resolve b24e6177 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e6177
            have b24e259454 : x = (M.op y (τ (M.op (σ x) (σ y)))) ∨ y = (M.op y y) ∨ x = (τ (M.op (σ x) (σ y))) := by
              first
              | (have i₁ := b24e84622 (τ (M.op (σ x) (σ y))) y
                 have i₂ := b24e39365
                 grind)
              | exact superpose b24e39365 b24e84622
              | (have j0 := b24e84622 x y
                 grind)
              | exact resolve b24e84622 b24e39365
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e39365 b24e84622
            have b24e259617 : x = (M.op y (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
              first
              | (have r₁ := b24e259454
                 have r₂ := b24e22
                 grind)
              | exact resolve b24e259454 b24e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e259454
            have b24e353879 : (M.op (M.op x x) x) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ x = (τ (M.op (σ x) (σ y))) := by
              first
              | (have i₁ := b24e37 (τ (M.op (σ x) (σ y))) y
                 have i₂ := b24e259617
                 grind)
              | exact superpose b24e259617 b24e37
              | exact resolve b24e37 b24e259617
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e37 b24e259617
            have b24e353944 : x = (M.op (τ (M.op (σ x) (σ y))) y) ∨ x = (τ (M.op (σ x) (σ y))) := by
              first
              | (have i₁ := b24e353879
                 have i₂ := b24e38 x
                 grind)
              | exact superpose b24e38 b24e353879
              | exact resolve b24e353879 b24e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e38 b24e353879
            have b24e364349 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
              first
              | (have i₁ := b24e36097 (σ x) (σ y) y
                 have i₂ := b24e353944
                 grind)
              | exact superpose b24e353944 b24e36097
              | exact resolve b24e36097 b24e353944
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e36097 b24e353944
            have b24e378226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
              first
              | (have i₁ := b24e16 (M.op (σ x) (σ y))
                 have i₂ := b24e364349
                 grind)
              | exact superpose b24e364349 b24e16
              | exact resolve b24e16 b24e364349
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e364349
            have b24e378228 : x = (τ (M.op (σ x) (σ y))) := by
              first
              | (have r₁ := b24e378226
                 have r₂ := b24e21
                 grind)
              | exact resolve b24e378226 b24e21
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e378226
            have b24e378266 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e16 (M.op (σ x) (σ y))
                 have i₂ := b24e378228
                 grind)
              | exact superpose b24e378228 b24e16
              | exact resolve b24e16 b24e378228
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e378228
            have b24e378394 : False := by grind
            exact b24e378394
          · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
                intro X0 X1 X2
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e23 : y ≠ (M.op y y) := by grind
              have b25e24 : x ≠ (M.op x y) := by grind
              have b25e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b25e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e28 : y = (M.op y x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e35 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y X0)) := by
                intro X0
                first
                | (have i₁ := b25e15 x y X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X2) X2) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 (M.op (M.op X1 X0) X2) X2 X3
                   have i₂ := b25e15 X0 X1 X2
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X0) (M.op X3 X2)) (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 X2 X3 (M.op (M.op X1 X0) (M.op X3 X2))
                   have i₂ := b25e15 X0 X1 (M.op X3 X2)
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e38 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e36 X0 X1 X2 x
                   have i₂ := b25e15 X1 X0 x
                   grind)
                | exact superpose b25e15 b25e36
                | exact resolve b25e36 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e36
              have b25e41 : ∀ X0 X1 : G, (M.op (M.op y X0) X0) = (M.op X1 (M.op (M.op x y) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 (M.op y X0) X0 X1
                   have i₂ := b25e35 X0
                   grind)
                | exact superpose b25e35 b25e15
                | exact resolve b25e15 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e43 : ∀ X0 : G, (M.op y x) = (M.op (M.op y X0) X0) := by
                intro X0
                first
                | (have i₁ := b25e41 X0 x
                   have i₂ := b25e15 y x x
                   grind)
                | exact superpose b25e15 b25e41
                | exact resolve b25e41 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e41
              have b25e44 : ∀ X0 : G, y = (M.op (M.op y X0) X0) := by
                intro X0
                first
                | (have i₁ := b25e43 X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e43
                | exact resolve b25e43 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e43
              have b25e58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X1 X0
                   have i₂ := b25e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b25e20 b25e21
                | (have j1 := b25e20 (σ X0) (σ X0)
                   grind)
                | exact resolve b25e21 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e61 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e18 X1 X0
                   have i₂ := b25e20 X2 X0
                   grind)
                | exact superpose b25e20 b25e18
                | (have j0 := b25e18 X1 X0
                   have j1 := b25e20 X2 X0
                   grind)
                | (have r₁ := b25e18 X0 X1
                   have r₂ := b25e20 X0 X1
                   grind)
                | (have r₁ := b25e18 X0 X1
                   have r₂ := b25e20 X1 X1
                   grind)
                | exact resolve b25e18 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e64 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b25e25
                   have i₂ := b25e20 X0 (σ y)
                   grind)
                | exact superpose b25e20 b25e25
                | (have j1 := b25e20 X0 (σ y)
                   grind)
                | (have r₁ := b25e25
                   have r₂ := b25e20 X0 (σ y)
                   grind)
                | (have r₁ := b25e25
                   have r₂ := b25e20 (σ y) (σ y)
                   grind)
                | exact resolve b25e25 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e65 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have j0 := b25e64 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e64
              have b25e66 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b25e61 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e61
              have b25e140 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op x y) (M.op X1 X0)) y) := by
                intro X0 X1
                first
                | (have i₁ := b25e37 y x X0 X1
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e37
                | exact resolve b25e37 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e37
              have b25e193 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
                intro X0
                first
                | (have i₁ := b25e21 X0 y
                   have i₂ := b25e65 (σ X0)
                   grind)
                | exact superpose b25e65 b25e21
                | (have j1 := b25e65 (σ X0)
                   grind)
                | exact resolve b25e21 b25e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e65
              have b25e351 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b25e66 X1 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e66
              have b25e475 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b25e26
                   have i₂ := b25e58 y x
                   grind)
                | exact superpose b25e58 b25e26
                | (have j1 := b25e58 y x
                   grind)
                | (have r₁ := b25e26
                   have r₂ := b25e58 y x
                   grind)
                | exact resolve b25e26 b25e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e58
              have b25e493 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b25e475
              have b25e503 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have r₁ := b25e493
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e493 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e493
              have b25e521 : ∀ X0 : G, (σ (k x y)) = (M.op (M.op (σ (k x y)) X0) X0) := by
                intro X0
                first
                | (have i₁ := b25e38 (σ x) (σ y) x
                   have i₂ := b25e503
                   grind)
                | exact superpose b25e503 b25e38
                | exact resolve b25e38 b25e503
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e38
              have b25e1175 : ∀ X0 : G, (σ (M.op y x)) = (M.op (M.op (σ (M.op y x)) X0) X0) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b25e521 X0
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e521
                | (have j1 := b25e20 y y
                   grind)
                | exact resolve b25e521 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e521
              have b25e1226 : ∀ X0 : G, (σ (M.op y x)) = (M.op (M.op (σ (M.op y x)) X0) X0) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have j0 := b25e1175 X0
                   grind)
                | (have r₁ := b25e1175 X0
                   have r₂ := b25e23
                   grind)
                | exact resolve b25e1175 b25e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1175
              have b25e1237 : ∀ X0 : G, (σ (M.op y x)) = (M.op (M.op (σ (M.op y x)) X0) X0) := by
                intro X0
                first
                | (have j0 := b25e1226 X0
                   grind)
                | (have r₁ := b25e1226 X0
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e1226 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1226
              have b25e1242 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) X0) := by
                intro X0
                first
                | (have i₁ := b25e1237 X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e1237
                | exact resolve b25e1237 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1237
              have b25e1278 : (σ y) = (M.op (σ (k x y)) (σ x)) := by
                first
                | (have i₁ := b25e1242 (σ x)
                   have i₂ := b25e503
                   grind)
                | exact superpose b25e503 b25e1242
                | exact resolve b25e1242 b25e503
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e1364 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b25e1278
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e1278
                | (have j1 := b25e20 y y
                   grind)
                | exact resolve b25e1278 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1278
              have b25e1394 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b25e1364
                   have r₂ := b25e23
                   grind)
                | exact resolve b25e1364 b25e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1364
              have b25e1399 : (σ y) = (M.op (σ (M.op y x)) (σ x)) := by
                first
                | (have r₁ := b25e1394
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e1394 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1394
              have b25e1401 : (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b25e1399
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e1399
                | exact resolve b25e1399 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1399
              have b25e1592 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b25e503
                   have i₂ := b25e1401
                   grind)
                | exact superpose b25e1401 b25e503
                | exact resolve b25e503 b25e1401
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e503
              have b25e1614 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) (σ y)) y) := by
                first
                | (have i₁ := b25e140 (σ x) (σ y)
                   have i₂ := b25e1401
                   grind)
                | exact superpose b25e1401 b25e140
                | exact resolve b25e140 b25e1401
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1401
              have b25e1975 : ∀ X0 : G, (σ (k (k x y) X0)) = (k (σ y) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b25e21 (k x y) X0
                   have i₂ := b25e1592
                   grind)
                | exact superpose b25e1592 b25e21
                | exact resolve b25e21 b25e1592
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e2006 : ∀ X0 : G, (σ (k (k x y) X0)) = (σ (k y X0)) := by
                intro X0
                first
                | (have i₁ := b25e1975 X0
                   have i₂ := b25e21 y X0
                   grind)
                | exact superpose b25e21 b25e1975
                | exact resolve b25e1975 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1975
              have b25e2155 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (k (k x y) y)) := by
                first
                | (have i₁ := b25e193 (k x y)
                   have i₂ := b25e1592
                   grind)
                | exact superpose b25e1592 b25e193
                | (have j0 := b25e193 y
                   grind)
                | exact resolve b25e193 b25e1592
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1592
              have b25e2236 : (M.op (σ y) (σ y)) = (σ (k (k x y) y)) := by
                first
                | (have r₁ := b25e2155
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e2155 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2155
              have b25e2243 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
                first
                | (have i₁ := b25e2236
                   have i₂ := b25e2006 y
                   grind)
                | exact superpose b25e2006 b25e2236
                | exact resolve b25e2236 b25e2006
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2006 b25e2236
              have b25e2247 : (σ y) ≠ (σ (k y y)) := by
                first
                | (have i₁ := b25e25
                   have i₂ := b25e2243
                   grind)
                | exact superpose b25e2243 b25e25
                | exact resolve b25e25 b25e2243
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2243
              have b25e2389 : (σ y) ≠ (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b25e2247
                   have i₂ := b25e20 y y
                   grind)
                | exact superpose b25e20 b25e2247
                | (have j1 := b25e20 y y
                   grind)
                | exact resolve b25e2247 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2247
              have b25e2390 : (σ y) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
              clear b25e2389
              have b25e2391 : (σ y) ≠ (σ (M.op y y)) := by
                first
                | (have r₁ := b25e2390
                   have r₂ := b25e23
                   grind)
                | exact resolve b25e2390 b25e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2390
              have b25e2434 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have j0 := b25e351 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e351
              have b25e2441 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b25e2434 X0
                   have j1 := b25e18 X0 X0
                   grind)
                | (have r₁ := b25e2434 x
                   have r₂ := b25e18 X0 x
                   grind)
                | exact resolve b25e2434 b25e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2434
              have b25e2514 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e21 X0 X0
                   have i₂ := b25e2441 (σ X0)
                   grind)
                | exact superpose b25e2441 b25e21
                | exact resolve b25e21 b25e2441
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e2526 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e2514 X0
                   have i₂ := b25e2441 X0
                   grind)
                | exact superpose b25e2441 b25e2514
                | exact resolve b25e2514 b25e2441
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2441 b25e2514
              have b25e2793 : (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
                first
                | (have i₁ := b25e1242 (σ y)
                   have i₂ := b25e2526 y
                   grind)
                | exact superpose b25e2526 b25e1242
                | exact resolve b25e1242 b25e2526
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1242 b25e2526
              have b25e3018 : (σ y) = (σ (M.op y y)) ∨ (σ (k (M.op y y) y)) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b25e193 (M.op y y)
                   have i₂ := b25e2793
                   grind)
                | exact superpose b25e2793 b25e193
                | (have j0 := b25e193 (M.op y y)
                   grind)
                | exact resolve b25e193 b25e2793
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e193
              have b25e3041 : (M.op (M.op (M.op x y) (σ y)) y) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b25e140 (σ y) (σ (M.op y y))
                   have i₂ := b25e2793
                   grind)
                | exact superpose b25e2793 b25e140
                | exact resolve b25e140 b25e2793
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e140 b25e2793
              have b25e3053 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have i₁ := b25e3041
                   have i₂ := b25e1614
                   grind)
                | exact superpose b25e1614 b25e3041
                | exact resolve b25e3041 b25e1614
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1614 b25e3041
              have b25e3067 : (σ (k (M.op y y) y)) = (M.op (σ y) (σ (M.op y y))) := by
                first
                | (have r₁ := b25e3018
                   have r₂ := b25e2391
                   grind)
                | exact resolve b25e3018 b25e2391
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2391 b25e3018
              have b25e3077 : (M.op (σ x) (σ y)) = (σ (k (M.op y y) y)) := by
                first
                | (have i₁ := b25e3067
                   have i₂ := b25e3053
                   grind)
                | exact superpose b25e3053 b25e3067
                | exact resolve b25e3067 b25e3053
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3053 b25e3067
              have b25e4844 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) := by
                first
                | (have i₁ := b25e3077
                   have i₂ := b25e20 (M.op y y) y
                   grind)
                | exact superpose b25e20 b25e3077
                | (have j1 := b25e20 y y
                   grind)
                | exact resolve b25e3077 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3077
              have b25e4887 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y y))) ∨ (M.op y y) = (M.op (M.op y y) y) := by
                first
                | (have r₁ := b25e4844
                   have r₂ := b25e23
                   grind)
                | exact resolve b25e4844 b25e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4844
              have b25e4900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op (M.op y y) y) := by
                first
                | (have i₁ := b25e4887
                   have i₂ := b25e35 y
                   grind)
                | exact superpose b25e35 b25e4887
                | exact resolve b25e4887 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35 b25e4887
              have b25e4913 : (M.op y y) = (M.op (M.op y y) y) := by
                first
                | (have r₁ := b25e4900
                   have r₂ := b25e22
                   grind)
                | exact resolve b25e4900 b25e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4900
              have b25e4926 : y = (M.op y y) := by
                first
                | (have i₁ := b25e4913
                   have i₂ := b25e44 y
                   grind)
                | exact superpose b25e44 b25e4913
                | exact resolve b25e4913 b25e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e44 b25e4913
              have b25e4932 : False := by grind
              exact b25e4932
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
              have b26e27 : x ≠ (M.op x x) := by grind
              have b26e28 : y ≠ (M.op y x) := by grind
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
              have b26e34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
              have b26e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X2) X2) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 (M.op (M.op X1 X0) X2) X2 X3
                   have i₂ := b26e15 X0 X1 X2
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X0) (M.op X3 X2)) (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X2 X3 (M.op (M.op X1 X0) (M.op X3 X2))
                   have i₂ := b26e15 X0 X1 (M.op X3 X2)
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e37 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 X0 X1 X2 x
                   have i₂ := b26e15 X1 X0 x
                   grind)
                | exact superpose b26e15 b26e35
                | exact resolve b26e35 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e35
              have b26e68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b26e20 b26e21
                | (have j1 := b26e20 (σ X0) (σ X0)
                   grind)
                | exact resolve b26e21 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e29 X1 X0
                   have i₂ := b26e20 (τ X1) X0
                   grind)
                | exact superpose b26e20 b26e29
                | (have j1 := b26e20 X0 X0
                   grind)
                | exact resolve b26e29 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e73 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
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
                   have r₂ := b26e20 X1 X1
                   grind)
                | exact resolve b26e18 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e78 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e73 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e73
              have b26e240 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k X2 (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e78 (σ X0) X2 (σ X1)
                   grind)
                | exact superpose b26e78 b26e21
                | (have j1 := b26e78 (σ X0) X2 (σ X1)
                   grind)
                | exact resolve b26e21 b26e78
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e246 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b26e78 X1 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e78
              have b26e319 : (σ x) ≠ (σ x) ∨ (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b26e26
                   have i₂ := b26e68 y x
                   grind)
                | exact superpose b26e68 b26e26
                | (have j1 := b26e68 y x
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e68 y x
                   grind)
                | exact resolve b26e26 b26e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e321 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e19 (σ X0) (σ X1)
                   have i₂ := b26e68 X1 X0
                   grind)
                | exact superpose b26e68 b26e19
                | (have j0 := b26e19 (σ X0) (σ X1)
                   have j1 := b26e68 X1 X0
                   grind)
                | (have r₁ := b26e19 (σ X0) (σ X0)
                   have r₂ := b26e68 X0 X1
                   grind)
                | (have r₁ := b26e19 (σ X1) (σ X0)
                   have r₂ := b26e68 X0 X1
                   grind)
                | exact resolve b26e19 b26e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68
              have b26e331 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have j0 := b26e321 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e321
              have b26e332 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have j0 := b26e331 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e331
              have b26e333 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b26e319
              have b26e341 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e332 X0 X1
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e332
                | (have j0 := b26e332 X0 X1
                   grind)
                | exact resolve b26e332 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e332
              have b26e342 : (σ (k x y)) = (M.op (σ y) (σ x)) := by
                first
                | (have r₁ := b26e333
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e333 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e333
              have b26e354 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ (k x y)) X0)) := by
                intro X0
                first
                | (have i₁ := b26e15 (σ x) (σ y) X0
                   have i₂ := b26e342
                   grind)
                | exact superpose b26e342 b26e15
                | exact resolve b26e15 b26e342
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e359 : ∀ X0 : G, (σ (k x y)) = (M.op (M.op (σ (k x y)) X0) X0) := by
                intro X0
                first
                | (have i₁ := b26e37 (σ x) (σ y) x
                   have i₂ := b26e342
                   grind)
                | exact superpose b26e342 b26e37
                | exact resolve b26e37 b26e342
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e37
              have b26e415 : ∀ X0 : G, (σ (M.op y x)) = (M.op (M.op (σ (M.op y x)) X0) X0) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b26e359 X0
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e359
                | (have j1 := b26e20 y y
                   grind)
                | exact resolve b26e359 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e359
              have b26e438 : ∀ X0 : G, (σ (M.op y x)) = (M.op (M.op (σ (M.op y x)) X0) X0) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have j0 := b26e415 X0
                   grind)
                | (have r₁ := b26e415 X0
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e415 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e415
              have b26e442 : ∀ X0 : G, (σ (M.op y x)) = (M.op (M.op (σ (M.op y x)) X0) X0) := by
                intro X0
                first
                | (have j0 := b26e438 X0
                   grind)
                | (have r₁ := b26e438 X0
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e438 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e438
              have b26e525 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X0)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b26e354 X0
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e354
                | (have j1 := b26e20 y y
                   grind)
                | exact resolve b26e354 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e354
              have b26e561 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X0)) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have j0 := b26e525 X0
                   grind)
                | (have r₁ := b26e525 X0
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e525 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e525
              have b26e572 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X0)) := by
                intro X0
                first
                | (have j0 := b26e561 X0
                   grind)
                | (have r₁ := b26e561 X0
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e561 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e561
              have b26e690 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op y x)) X0) X0) = (M.op (M.op (M.op X1 X2) (M.op (σ x) (σ y))) (M.op X2 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e36 X2 X1 (M.op (σ (M.op y x)) X0) X0
                   have i₂ := b26e572 X0
                   grind)
                | exact superpose b26e572 b26e36
                | exact resolve b26e36 b26e572
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e572
              have b26e709 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ (M.op y x)) X0) X0) := by
                intro X0
                first
                | (have i₁ := b26e690 X0 x x
                   have i₂ := b26e36 x x (σ y) (σ x)
                   grind)
                | exact superpose b26e36 b26e690
                | exact resolve b26e690 b26e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e36 b26e690
              have b26e726 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
                first
                | (have i₁ := b26e709 x
                   have i₂ := b26e442 x
                   grind)
                | exact superpose b26e442 b26e709
                | exact resolve b26e709 b26e442
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e442 b26e709
              have b26e909 : (σ (k x y)) = (σ (M.op y x)) := by
                first
                | (have i₁ := b26e342
                   have i₂ := b26e726
                   grind)
                | exact superpose b26e726 b26e342
                | exact resolve b26e342 b26e726
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1198 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have j0 := b26e246 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e246
              have b26e1203 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b26e1198 X0
                   have j1 := b26e18 X0 X0
                   grind)
                | (have r₁ := b26e1198 x
                   have r₂ := b26e18 X0 x
                   grind)
                | exact resolve b26e1198 b26e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1198
              have b26e1241 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e21 X0 X0
                   have i₂ := b26e1203 (σ X0)
                   grind)
                | exact superpose b26e1203 b26e21
                | exact resolve b26e21 b26e1203
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1252 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e1241 X0
                   have i₂ := b26e1203 X0
                   grind)
                | exact superpose b26e1203 b26e1241
                | exact resolve b26e1241 b26e1203
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1203 b26e1241
              have b26e1472 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e70 X0 (σ X0)
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e70
                | (have j0 := b26e70 X1 X1
                   grind)
                | exact resolve b26e70 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e70
              have b26e1553 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e1472 X0 X1
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e1472
                | (have j0 := b26e1472 X1 X1
                   grind)
                | exact resolve b26e1472 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1472
              have b26e4855 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e341 (τ X0) X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e341
                | (have j0 := b26e341 X0 X1
                   grind)
                | exact resolve b26e341 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e4875 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (k X1 (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e341 X0 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e341
                | (have j0 := b26e341 X1 (τ X0)
                   grind)
                | exact resolve b26e341 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e341
              have b26e5044 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (σ (k X1 (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e4875 X0 X1
                   have i₂ := b26e30 X0 X1
                   grind)
                | exact superpose b26e30 b26e4875
                | (have j0 := b26e4875 X0 X1
                   grind)
                | exact resolve b26e4875 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4875
              have b26e5062 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e4855 X0 X1
                   have i₂ := b26e29 X0 X1
                   grind)
                | exact superpose b26e29 b26e4855
                | (have j0 := b26e4855 X0 X1
                   grind)
                | exact resolve b26e4855 b26e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4855
              have b26e5087 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e5044 X0 X1
                   have i₂ := b26e30 X0 X1
                   grind)
                | exact superpose b26e30 b26e5044
                | (have j0 := b26e5044 X0 X1
                   grind)
                | exact resolve b26e5044 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30 b26e5044
              have b26e5093 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e5062 X0 X1
                   have i₂ := b26e1252 X1
                   grind)
                | exact superpose b26e1252 b26e5062
                | (have j0 := b26e5062 X0 X1
                   grind)
                | exact resolve b26e5062 b26e1252
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1252 b26e5062
              have b26e5110 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e5093 X0 X1
                   have i₂ := b26e29 X0 X1
                   grind)
                | exact superpose b26e29 b26e5093
                | (have j0 := b26e5093 X0 X1
                   grind)
                | exact resolve b26e5093 b26e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29 b26e5093
              have b26e7095 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                intro X0
                first
                | (have i₁ := b26e22
                   have i₂ := b26e240 x y X0
                   grind)
                | exact superpose b26e240 b26e22
                | (have j1 := b26e240 x y X0
                   grind)
                | exact resolve b26e22 b26e240
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e240
              have b26e7280 : ∀ X0 : G, (σ y) = (σ (k x y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b26e7095 X0
                   have i₂ := b26e342
                   grind)
                | exact superpose b26e342 b26e7095
                | (have j0 := b26e7095 X0
                   grind)
                | exact resolve b26e7095 b26e342
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e342 b26e7095
              have b26e7328 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y x)) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b26e7280 X0
                   have i₂ := b26e909
                   grind)
                | exact superpose b26e909 b26e7280
                | (have j0 := b26e7280 X0
                   grind)
                | exact resolve b26e7280 b26e909
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e909 b26e7280
              have b26e57316 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e5087 X0 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e5087
                | (have j0 := b26e5087 X1 X1
                   grind)
                | exact resolve b26e5087 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5087
              have b26e58155 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b26e57316 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e57316
              have b26e64209 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (M.op X0 X0)
                   have i₂ := b26e5110 X1 X0
                   grind)
                | exact superpose b26e5110 b26e16
                | (have j1 := b26e5110 X1 X0
                   grind)
                | exact resolve b26e16 b26e5110
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5110
              have b26e64357 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e64209 X0 X1
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e64209
                | (have j0 := b26e64209 X0 X1
                   grind)
                | exact resolve b26e64209 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e64209
              have b26e112617 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e64357 X1 (σ X0)
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e64357
                | (have j0 := b26e64357 X1 X1
                   grind)
                | exact resolve b26e64357 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e64357
              have b26e240151 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e112617 y x
                   grind)
                | exact superpose b26e112617 b26e22
                | (have j1 := b26e112617 y x
                   grind)
                | exact resolve b26e22 b26e112617
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e112617
              have b26e240190 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have r₁ := b26e240151
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e240151 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e240151
              have b26e242720 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b26e240190
                   have i₂ := b26e1553 y x
                   grind)
                | exact superpose b26e1553 b26e240190
                | (have j1 := b26e1553 x x
                   grind)
                | (have r₁ := b26e240190
                   have r₂ := b26e1553 y x
                   grind)
                | exact resolve b26e240190 b26e1553
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1553 b26e240190
              have b26e242732 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by grind
              clear b26e242720
              have b26e242740 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
                first
                | (have r₁ := b26e242732
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e242732 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e242732
              have b26e242744 : (σ (M.op x y)) = (σ y) := by
                first
                | (have r₁ := b26e242740
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e242740 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e242740
              have b26e242752 : (M.op x y) = (τ (σ y)) := by
                first
                | (have i₁ := b26e16 (M.op x y)
                   have i₂ := b26e242744
                   grind)
                | exact superpose b26e242744 b26e16
                | exact resolve b26e16 b26e242744
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e242946 : y = (M.op x y) := by
                first
                | (have i₁ := b26e242752
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e242752
                | exact resolve b26e242752 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e242752
              have b26e243280 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
                first
                | (have i₁ := b26e58155 y x
                   have i₂ := b26e242946
                   grind)
                | exact superpose b26e242946 b26e58155
                | (have j0 := b26e58155 y x
                   grind)
                | (have r₁ := b26e58155 y x
                   have r₂ := b26e242946
                   grind)
                | exact resolve b26e58155 b26e242946
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e58155 b26e242946
              have b26e243368 : x = (M.op x x) ∨ y = (k y x) := by grind
              clear b26e243280
              have b26e243371 : y = (k y x) := by
                first
                | (have r₁ := b26e243368
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e243368 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e243368
              have b26e243453 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op y x)) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b26e7328 X0
                   have i₂ := b26e243371
                   grind)
                | exact superpose b26e243371 b26e7328
                | (have j0 := b26e7328 X0
                   grind)
                | exact resolve b26e7328 b26e243371
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e7328
              have b26e243503 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (σ (M.op y x)) := by
                intro X0
                first
                | (have j0 := b26e243453 X0
                   grind)
                | (have r₁ := b26e243453 X0
                   have r₂ := b26e242744
                   grind)
                | exact resolve b26e243453 b26e242744
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e242744 b26e243453
              have b26e275470 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ (σ y) = (σ (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b26e34 X0 x
                   have i₂ := b26e243503 X0
                   grind)
                | exact superpose b26e243503 b26e34
                | exact resolve b26e34 b26e243503
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e34 b26e243503
              have b26e285794 : (τ (σ (M.op y x))) = (k (τ (σ y)) x) ∨ (σ y) = (σ (M.op y x)) := by
                first
                | (have i₁ := b26e275470 (σ y)
                   have i₂ := b26e726
                   grind)
                | exact superpose b26e726 b26e275470
                | exact resolve b26e275470 b26e726
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e726 b26e275470
              have b26e285869 : (k y x) = (τ (σ (M.op y x))) ∨ (σ y) = (σ (M.op y x)) := by
                first
                | (have i₁ := b26e285794
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e285794
                | exact resolve b26e285794 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e285794
              have b26e285902 : (M.op y x) = (k y x) ∨ (σ y) = (σ (M.op y x)) := by
                first
                | (have i₁ := b26e285869
                   have i₂ := b26e16 (M.op y x)
                   grind)
                | exact superpose b26e16 b26e285869
                | exact resolve b26e285869 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e285869
              have b26e285918 : y = (M.op y x) ∨ (σ y) = (σ (M.op y x)) := by
                first
                | (have i₁ := b26e285902
                   have i₂ := b26e243371
                   grind)
                | exact superpose b26e243371 b26e285902
                | exact resolve b26e285902 b26e243371
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e243371 b26e285902
              have b26e285929 : (σ y) = (σ (M.op y x)) := by
                first
                | (have r₁ := b26e285918
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e285918 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e285918
              have b26e287531 : (M.op y x) = (τ (σ y)) := by
                first
                | (have i₁ := b26e16 (M.op y x)
                   have i₂ := b26e285929
                   grind)
                | exact superpose b26e285929 b26e16
                | exact resolve b26e16 b26e285929
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e285929
              have b26e287673 : y = (M.op y x) := by
                first
                | (have i₁ := b26e287531
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e287531
                | exact resolve b26e287531 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e287531
              have b26e287709 : False := by grind
              exact b26e287709
