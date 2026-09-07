import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation643 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law643 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
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
      have b0e38 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
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
      have b0e41 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e37 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e37
        | exact resolve b0e37 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e42 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e38 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e38
        | exact resolve b0e38 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e63 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e41 (σ x)
           grind)
        | exact superpose b0e41 b0e18
        | exact resolve b0e18 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e66 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e63
           have i₂ := b0e42 x
           grind)
        | exact superpose b0e42 b0e63
        | exact resolve b0e63 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e63
      have b0e67 : False := by grind
      exact b0e67
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b1e26 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e78 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e21
             have i₂ := b1e17 (σ y) X0
             grind)
          | exact superpose b1e17 b1e21
          | (have j1 := b1e17 X0 X0
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 X0 (σ y)
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 (σ y) x
             grind)
          | exact resolve b1e21 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e84 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e78 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78
        have b1e104 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e27 X0 y
             have i₂ := b1e26 (τ X0)
             grind)
          | exact superpose b1e26 b1e27
          | exact resolve b1e27 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e27
        have b1e112 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e104 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e104
          | exact resolve b1e104 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104
        have b1e217 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e112 (σ y)
             have i₂ := b1e84 (σ y)
             grind)
          | exact superpose b1e84 b1e112
          | (have j1 := b1e84 (σ y)
             grind)
          | exact resolve b1e112 b1e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84 b1e112
        have b1e222 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e217
        have b1e226 : False := by grind
        exact b1e226
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
        have b2e53 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b2e57 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e53 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e53
          | exact resolve b2e53 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e63 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ y) x
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e78 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b2e63 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e81 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e78 X0
             have i₂ := b2e57 X0
             grind)
          | exact superpose b2e57 b2e78
          | (have j0 := b2e78 X0
             grind)
          | exact resolve b2e78 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e78
        have b2e138 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have j0 := b2e81 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81
        have b2e139 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e138
        have b2e144 : False := by grind
        exact b2e144
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b3e30 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
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
        have b3e37 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e38 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e38
          | exact resolve b3e38 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e46 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e37 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e37
          | exact resolve b3e37 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e49 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
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
        have b3e50 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b3e46 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e46
          | exact resolve b3e46 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e62 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e16 x X0
             have i₂ := b3e50 x
             grind)
          | exact superpose b3e50 b3e16
          | (have j0 := b3e16 x X0
             grind)
          | (have r₁ := b3e16 x x
             have r₂ := b3e50 x
             grind)
          | exact resolve b3e16 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e63 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b3e62 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62
        have b3e93 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e49 (σ x)
             grind)
          | exact superpose b3e49 b3e19
          | exact resolve b3e19 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e1047 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e30 x
             have i₂ := b3e63 y
             grind)
          | exact superpose b3e63 b3e30
          | (have j1 := b3e63 y
             grind)
          | exact resolve b3e30 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e63
        have b3e1061 : y = (M.op y y) := by
          first
          | (have r₁ := b3e1047
             have r₂ := b3e93
             grind)
          | exact resolve b3e1047 b3e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e93 b3e1047
        have b3e1067 : False := by grind
        exact b3e1067
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y y) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e33 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e33 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e33
            | exact resolve b4e33 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e46 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e42 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e42
            | exact resolve b4e42 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e56 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e17 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) X0
               grind)
            | (have r₁ := b4e17 (σ x) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e58 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e46 x
               grind)
            | exact superpose b4e46 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 x x
               have r₂ := b4e46 x
               grind)
            | exact resolve b4e17 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e59 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e58 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58
          have b4e61 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e56 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e161 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e61 (σ X0)
               grind)
            | exact superpose b4e61 b4e19
            | (have j1 := b4e61 (σ X0)
               grind)
            | exact resolve b4e19 b4e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61
          have b4e3580 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e161 y
               grind)
            | exact superpose b4e161 b4e23
            | (have j1 := b4e161 y
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e161 y
               grind)
            | exact resolve b4e23 b4e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e161
          have b4e3595 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b4e3580
          have b4e3602 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e3595
               grind)
            | exact superpose b4e3595 b4e20
            | exact resolve b4e20 b4e3595
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3595
          have b4e3677 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e3602
               have i₂ := b4e59 y
               grind)
            | exact superpose b4e59 b4e3602
            | (have j1 := b4e59 y
               grind)
            | exact resolve b4e3602 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59 b4e3602
          have b4e3689 : y = (M.op y y) := by grind
          clear b4e3677
          have b4e3693 : False := by grind
          exact b4e3693
        · have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e16 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 X0 x
               grind)
            | (have r₁ := b5e16 X0 x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e26 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b5e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25
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
          have b5e30 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 x
               have i₂ := b5e26 (τ X0)
               grind)
            | exact superpose b5e26 b5e27
            | exact resolve b5e27 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e27
          have b5e34 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e30 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e30
            | exact resolve b5e30 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e76 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 X0 (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) x
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e81 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e76 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e148 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e34 (σ x)
               have i₂ := b5e81 (σ x)
               grind)
            | exact superpose b5e81 b5e34
            | (have j1 := b5e81 (σ x)
               grind)
            | exact resolve b5e34 b5e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e81
          have b5e151 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e148
          have b5e155 : False := by grind
          exact b5e155
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
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
        have b6e72 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e79 : ∀ X0 : G, (M.op y X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e72 X0
             grind)
          | (have r₁ := b6e72 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e72 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e72 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e975 : y ≠ y ∨ y = (M.op y y) := by
          first
          | (have j0 := b6e79 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e976 : y = (M.op y y) := by grind
        clear b6e975
        have b6e982 : False := by grind
        exact b6e982
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e16 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 X0 (σ x)
               grind)
            | (have r₁ := b7e16 X0 (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e26 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have j0 := b7e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25
          have b7e30 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 x
               have i₂ := b7e26 (σ X0)
               grind)
            | exact superpose b7e26 b7e19
            | exact resolve b7e19 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e33 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b7e14 (k X0 x)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e14
            | exact resolve b7e14 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e34 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e33
            | exact resolve b7e33 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 X0 X1
               have i₂ := b7e18 X2 X0
               grind)
            | exact superpose b7e18 b7e17
            | (have j0 := b7e17 X0 X1
               have j1 := b7e18 X1 X1
               grind)
            | (have r₁ := b7e17 X1 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e17 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | exact resolve b7e17 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e82 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e65 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e844 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e82 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e845 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e844 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e844
          have b7e846 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e845 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e845
          have b7e1187 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e34 x
               have i₂ := b7e846 x
               grind)
            | exact superpose b7e846 b7e34
            | (have j1 := b7e846 x
               grind)
            | exact resolve b7e34 b7e846
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e846
          have b7e1189 : x = (M.op x x) := by grind
          clear b7e1187
          have b7e1215 : False := by grind
          exact b7e1215
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e58 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ y) X0
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) x
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e64 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e58 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e136 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e64 (σ X0)
               grind)
            | exact superpose b8e64 b8e19
            | (have j1 := b8e64 (σ X0)
               grind)
            | exact resolve b8e19 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e3252 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e136 x
               grind)
            | exact superpose b8e136 b8e20
            | (have j1 := b8e136 x
               grind)
            | exact resolve b8e20 b8e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136
          have b8e3317 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e3252
               have r₂ := b8e24
               grind)
            | exact resolve b8e3252 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3252
          have b8e3325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e3317
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e3317
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e3317 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3317
          have b8e3343 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e3325
          have b8e3350 : y = (M.op y y) := by
            first
            | (have r₁ := b8e3343
               have r₂ := b8e22
               grind)
            | exact resolve b8e3343 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3343
          have b8e3351 : False := by grind
          exact b8e3351

/-- `Equation839`: `x = x ◇ ((y ◇ x) ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_y_pxy_Equation839 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law839 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law839.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e87 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
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
      have b0e120 : x = (M.op x y) := by
        first
        | (have i₁ := b0e87 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e87
        | exact resolve b0e87 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e123 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e87 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e87
        | exact resolve b0e87 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e273 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e123
           grind)
        | exact superpose b0e123 b0e18
        | exact resolve b0e18 b0e123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e123
      have b0e285 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e273
           have i₂ := b0e120
           grind)
        | exact superpose b0e120 b0e273
        | exact resolve b0e273 b0e120
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e120 b0e273
      have b0e286 : False := by grind
      exact b0e286
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : x = (k x y) := by grind
        have b1e40 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e43 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e40
        have b1e45 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e43
             have r₂ := b1e21
             grind)
          | exact resolve b1e43 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e47 : (σ y) = (σ (k x y)) := by
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
        have b1e48 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e47
          | exact resolve b1e47 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e47
        have b1e52 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e13
          | exact resolve b1e13 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : x = y := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e52
          | exact resolve b1e52 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e72 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e24
          | exact resolve b1e24 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e53
        have b1e74 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e72
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e72
          | exact resolve b1e72 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e75 : False := by grind
        exact b1e75
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b2e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e75 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
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
        have b2e106 : x = (M.op x y) := by
          first
          | (have i₁ := b2e75 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e75
          | exact resolve b2e75 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75
        have b2e683 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e50 x y
             grind)
          | exact superpose b2e50 b2e19
          | (have j1 := b2e50 x y
             grind)
          | exact resolve b2e19 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e739 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e683
             have r₂ := b2e21
             grind)
          | exact resolve b2e683 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e683
        have b2e744 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e739
             have r₂ := b2e22
             grind)
          | exact resolve b2e739 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e739
        have b2e745 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e744
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e744
          | exact resolve b2e744 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e744
        have b2e746 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e745
             have i₂ := b2e106
             grind)
          | exact superpose b2e106 b2e745
          | exact resolve b2e745 b2e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e106 b2e745
        have b2e747 : False := by grind
        exact b2e747
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e26 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e25
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e25
          | exact resolve b3e25 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e26
             grind)
          | exact superpose b3e26 b3e13
          | exact resolve b3e13 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e28 : x = (k x y) := by
          first
          | (have i₁ := b3e27
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e27
          | exact resolve b3e27 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e52 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
        have b3e55 : y = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e52
        have b3e57 : y = (k x y) := by
          first
          | (have r₁ := b3e55
             have r₂ := b3e20
             grind)
          | exact resolve b3e55 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e58 : x = y := by
          first
          | (have i₁ := b3e57
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e57
          | exact resolve b3e57 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e57
        have b3e61 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e58
             grind)
          | exact superpose b3e58 b3e24
          | exact resolve b3e24 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e64 : (σ x) ≠ (σ y) := by
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
        have b3e65 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e64
             have i₂ := b3e58
             grind)
          | exact superpose b3e58 b3e64
          | exact resolve b3e64 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58 b3e64
        have b3e66 : False := by grind
        exact b3e66
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b5e35 : ∀ X0 : G, y = (M.op y (M.op x (M.op X0 x))) := by
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
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X2 X1)) = (M.op (M.op (M.op X1 X0) (M.op X2 X1)) (M.op X0 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X1 X0) (M.op X2 X1)) X0 X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 : G, (M.op X0 (M.op (M.op y X0) x)) = X0 := by
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
          have b5e39 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
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
          have b5e42 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X2 X1)) = (M.op X0 X0) ∨ (M.op (M.op X1 X0) (M.op X2 X1)) = (k X0 (M.op (M.op X1 X0) (M.op X2 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X0 (M.op (M.op X1 X0) (M.op X2 X1))
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 X0 (M.op (M.op X1 X0) (M.op X2 X1))
               grind)
            | (have r₁ := b5e17 X0 (M.op (M.op X1 X0) (M.op X2 X1))
               have r₂ := b5e13 X0 X1 X2
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e46 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X1)) = (k X0 (M.op (M.op X1 X0) (M.op X2 X1))) ∨ (M.op (M.op X1 X0) (M.op X2 X1)) = (M.op X0 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e43 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e47 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e42
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
          have b5e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e61 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x (M.op X0 x)) (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b5e37 (M.op x (M.op X0 x))
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e37
            | exact resolve b5e37 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e67 : ∀ X0 : G, (M.op X0 (M.op x X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x (M.op y (M.op x X0))
               have i₂ := b5e37 (M.op x X0)
               grind)
            | exact superpose b5e37 b5e13
            | exact resolve b5e13 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e68 : y = (M.op y x) := by
            first
            | (have i₁ := b5e35 (M.op y x)
               have i₂ := b5e37 x
               grind)
            | exact superpose b5e37 b5e35
            | exact resolve b5e35 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e72 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x (M.op X0 x)) y) := by
            intro X0
            first
            | (have i₁ := b5e61 X0
               have i₂ := b5e68
               grind)
            | exact superpose b5e68 b5e61
            | exact resolve b5e61 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e76 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e39 X0 (M.op (M.op x x) X0) X1
               have i₂ := b5e39 x x X0
               grind)
            | exact superpose b5e39 b5e39
            | exact resolve b5e39 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e105 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e180 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e76 X1 X1
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e76 X0 X1
               have i₂ := b5e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b5e18 b5e76
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e76 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e195 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e180 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180
          have b5e199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e55 (σ X1) (σ X0)
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e55
            | (have j0 := b5e55 (σ X1) (σ X0)
               grind)
            | exact resolve b5e55 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e674 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op X2 (σ X0)))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X1) (σ X0) X2
               have i₂ := b5e52 X0 X1
               grind)
            | exact superpose b5e52 b5e13
            | (have j1 := b5e52 X0 X1
               grind)
            | exact resolve b5e13 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e708 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e76 (σ X1) (σ X1)
               have i₂ := b5e52 X1 X0
               grind)
            | exact superpose b5e52 b5e76
            | (have j1 := b5e52 X1 X0
               grind)
            | exact resolve b5e76 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e711 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e713 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e708 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e708
          have b5e805 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op (M.op y X0) x) (M.op X0 (M.op X1 X0))) ∨ (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op y X0) x) (M.op (M.op y X0) x)) := by
            intro X0 X1
            first
            | (have i₁ := b5e46 (M.op (M.op y X0) x) X0 x
               have i₂ := b5e37 X0
               grind)
            | exact superpose b5e37 b5e46
            | exact resolve b5e46 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e833 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X3 X1)) X4) (M.op (M.op X0 X1) (M.op X2 X0))) = (k X4 (M.op (M.op (M.op X1 (M.op X3 X1)) X4) (M.op (M.op X0 X1) (M.op X2 X0)))) ∨ (M.op (M.op (M.op X1 (M.op X3 X1)) X4) (M.op (M.op X0 X1) (M.op X2 X0))) = (M.op X4 X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e46 X0 (M.op X0 (M.op X3 X0)) (M.op (M.op X1 X0) (M.op X2 X1))
               have i₂ := b5e36 X0 X1 X2 X3
               grind)
            | exact superpose b5e36 b5e46
            | exact resolve b5e46 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e46
          have b5e864 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X4) (M.op (M.op X0 X1) (M.op X2 X0))) = (k X4 (M.op (M.op X1 X4) (M.op (M.op X0 X1) (M.op X2 X0)))) ∨ (M.op (M.op (M.op X1 (M.op X3 X1)) X4) (M.op (M.op X0 X1) (M.op X2 X0))) = (M.op X4 X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e833 X0 X1 X2 X0 X4
               have i₂ := b5e76 X0 X1
               grind)
            | exact superpose b5e76 b5e833
            | (have j0 := b5e833 X0 X1 X2 X3 X4
               grind)
            | exact resolve b5e833 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e833
          have b5e874 : ∀ X0 X1 : G, (k (M.op (M.op y X0) x) X0) = X0 ∨ (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op y X0) x) (M.op (M.op y X0) x)) := by
            intro X0 X1
            first
            | (have i₁ := b5e805 X1 X0
               have i₂ := b5e76 X0 X1
               grind)
            | exact superpose b5e76 b5e805
            | (have j0 := b5e805 X0 X1
               grind)
            | exact resolve b5e805 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e805
          have b5e880 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X4) (M.op (M.op X0 X1) (M.op X2 X0))) = (k X4 (M.op (M.op X1 X4) (M.op (M.op X0 X1) (M.op X2 X0)))) ∨ (M.op (M.op X1 X4) (M.op (M.op X0 X1) (M.op X2 X0))) = (M.op X4 X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e864 X0 X1 X2 x X4
               have i₂ := b5e76 x X1
               grind)
            | exact superpose b5e76 b5e864
            | (have j0 := b5e864 X0 X1 X2 x X4
               grind)
            | exact resolve b5e864 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e864
          have b5e889 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) (M.op (M.op y X0) x)) = X0 ∨ (k (M.op (M.op y X0) x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e874 X0 x
               have i₂ := b5e76 x X0
               grind)
            | exact superpose b5e76 b5e874
            | (have j0 := b5e874 X0 x
               grind)
            | exact resolve b5e874 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e874
          have b5e901 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b5e105
          have b5e918 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e901 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e901
            | exact resolve b5e901 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e901
          have b5e1514 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e918 X0
               have i₂ := b5e195 (τ (M.op (σ X0) (σ X0))) X0
               grind)
            | exact superpose b5e195 b5e918
            | (have j1 := b5e195 (τ (M.op (σ X0) (σ X0))) X0
               grind)
            | exact resolve b5e918 b5e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e195 b5e918
          have b5e1521 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have j0 := b5e1514 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1514
          have b5e1677 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e1521 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1521
            | exact resolve b5e1521 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1685 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (τ (M.op (σ X0) (σ X0))) X1) X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (τ (M.op (σ X0) (σ X0))) X0
               have i₂ := b5e1521 X0
               grind)
            | exact superpose b5e1521 b5e13
            | exact resolve b5e13 b5e1521
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1521
          have b5e2043 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e76 (τ X0) (τ (M.op X0 X0))
               have i₂ := b5e1677 X0
               grind)
            | exact superpose b5e1677 b5e76
            | exact resolve b5e76 b5e1677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1677
          have b5e11310 : ∀ X0 : G, (M.op (M.op y X0) x) = (k (M.op (M.op y X0) x) X0) ∨ (k (M.op (M.op y X0) x) X0) = X0 := by
            intro X0
            grind
          clear b5e889
          have b5e13387 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e711 x y
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e711
            | (have j0 := b5e711 x y
               grind)
            | exact resolve b5e711 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e711
          have b5e13404 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e13387
               have r₂ := b5e23
               grind)
            | exact resolve b5e13387 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13387
          have b5e13410 : (σ x) ≠ (σ y) := by
            first
            | (have r₁ := b5e13404
               have r₂ := b5e24
               grind)
            | exact resolve b5e13404 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13404
          have b5e16533 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e76 (σ X0) (σ X1)
               have i₂ := b5e199 X0 X1
               grind)
            | exact superpose b5e199 b5e76
            | (have j1 := b5e199 X0 X1
               grind)
            | exact resolve b5e76 b5e199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e199
          have b5e20667 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ x)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e674 x y X0
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e674
            | (have j0 := b5e674 x y x
               grind)
            | exact resolve b5e674 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e674
          have b5e20842 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e20667 X0
               grind)
            | (have r₁ := b5e20667 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e20667 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20667
          have b5e20852 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have j0 := b5e20842 X0
               grind)
            | (have r₁ := b5e20842 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e20842 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20842
          have b5e20896 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e20852 (M.op (τ (M.op (σ (σ x)) (σ (σ x)))) (σ y))
               have i₂ := b5e1685 (σ x) (σ y)
               grind)
            | exact superpose b5e1685 b5e20852
            | exact resolve b5e20852 b5e1685
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1685
          have b5e21791 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
            first
            | (have i₁ := b5e2043 (σ y)
               have i₂ := b5e20896
               grind)
            | exact superpose b5e20896 b5e2043
            | exact resolve b5e2043 b5e20896
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2043 b5e20896
          have b5e21897 : y = (M.op y y) := by
            first
            | (have i₁ := b5e21791
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e21791
            | exact resolve b5e21791 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21791
          have b5e34996 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op X0 x)) (M.op (M.op X1 (M.op x (M.op X0 x))) (M.op X2 X1))) = (k y (M.op (M.op x (M.op X0 x)) (M.op (M.op X1 (M.op x (M.op X0 x))) (M.op X2 X1)))) ∨ (M.op y y) = (M.op (M.op x (M.op X0 x)) (M.op (M.op X1 (M.op x (M.op X0 x))) (M.op X2 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e880 X0 (M.op x (M.op X0 x)) X2 y
               have i₂ := b5e72 X0
               grind)
            | exact superpose b5e72 b5e880
            | exact resolve b5e880 b5e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72 b5e880
          have b5e35529 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 x)) = (k y (M.op x (M.op X0 x))) ∨ (M.op y y) = (M.op (M.op x (M.op X0 x)) (M.op (M.op X1 (M.op x (M.op X0 x))) (M.op X2 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34996 X0 X1 X2
               have i₂ := b5e13 (M.op x (M.op X0 x)) X1 X2
               grind)
            | exact superpose b5e13 b5e34996
            | (have j0 := b5e34996 X0 X1 X2
               grind)
            | exact resolve b5e34996 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34996
          have b5e35745 : ∀ X0 X1 X2 : G, x = (k y x) ∨ (M.op y y) = (M.op (M.op x (M.op X0 x)) (M.op (M.op X1 (M.op x (M.op X0 x))) (M.op X2 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35529 X0 X1 X2
               have i₂ := b5e76 X0 x
               grind)
            | exact superpose b5e76 b5e35529
            | (have j0 := b5e35529 X0 X1 X2
               grind)
            | exact resolve b5e35529 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35529
          have b5e35848 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op y y) ∨ x = (k y x) := by
            intro X0
            first
            | (have i₁ := b5e35745 X0 x x
               have i₂ := b5e13 (M.op x (M.op X0 x)) x x
               grind)
            | exact superpose b5e13 b5e35745
            | exact resolve b5e35745 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35745
          have b5e35874 : ∀ X0 : G, y = (M.op x (M.op X0 x)) ∨ x = (k y x) := by
            intro X0
            first
            | (have i₁ := b5e35848 X0
               have i₂ := b5e21897
               grind)
            | exact superpose b5e21897 b5e35848
            | exact resolve b5e35848 b5e21897
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21897 b5e35848
          have b5e35885 : x = (k y x) ∨ x = y := by
            first
            | (have i₁ := b5e35874 x
               have i₂ := b5e76 x x
               grind)
            | exact superpose b5e76 b5e35874
            | exact resolve b5e35874 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35874
          have b5e111526 : (M.op y x) = (k (M.op y x) (M.op x y)) ∨ (M.op x y) = (k (M.op y x) (M.op x y)) := by
            first
            | (have i₁ := b5e11310 (M.op x y)
               have i₂ := b5e67 y
               grind)
            | exact superpose b5e67 b5e11310
            | exact resolve b5e11310 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e11310
          have b5e111600 : (M.op y x) = (k (M.op y x) x) ∨ (M.op x y) = (k (M.op y x) (M.op x y)) := by
            first
            | (have i₁ := b5e111526
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e111526
            | exact resolve b5e111526 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e111526
          have b5e111611 : y = (k y x) ∨ (M.op x y) = (k (M.op y x) (M.op x y)) := by
            first
            | (have i₁ := b5e111600
               have i₂ := b5e68
               grind)
            | exact superpose b5e68 b5e111600
            | exact resolve b5e111600 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e111600
          have b5e111619 : x = (k (M.op y x) x) ∨ y = (k y x) := by
            first
            | (have i₁ := b5e111611
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e111611
            | exact resolve b5e111611 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e111611
          have b5e111623 : y = (k y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b5e111619
               have i₂ := b5e68
               grind)
            | exact superpose b5e68 b5e111619
            | exact resolve b5e111619 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68 b5e111619
          have b5e111650 : x ≠ y ∨ x = (k y x) := by grind
          clear b5e111623
          have b5e111666 : x = (k y x) := by
            first
            | (have r₁ := b5e111650
               have r₂ := b5e35885
               grind)
            | exact resolve b5e111650 b5e35885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35885 b5e111650
          have b5e175154 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e16533 y x
               have i₂ := b5e111666
               grind)
            | exact superpose b5e111666 b5e16533
            | (have j0 := b5e16533 x x
               grind)
            | exact resolve b5e16533 b5e111666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16533
          have b5e175161 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b5e175154
               have r₂ := b5e13410
               grind)
            | exact resolve b5e175154 b5e13410
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13410 b5e175154
          have b5e180057 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e76 (σ y) (σ x)
               have i₂ := b5e175161
               grind)
            | exact superpose b5e175161 b5e76
            | exact resolve b5e76 b5e175161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e175161
          have b5e180116 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b5e180057
               have r₂ := b5e24
               grind)
            | exact resolve b5e180057 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180057
          have b5e181186 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b5e20852 (σ x)
               have i₂ := b5e180116
               grind)
            | exact superpose b5e180116 b5e20852
            | exact resolve b5e20852 b5e180116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20852 b5e180116
          have b5e187365 : (σ y) = (M.op (σ y) (σ (k y x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e181186
               have i₂ := b5e713 x y
               grind)
            | exact superpose b5e713 b5e181186
            | (have j1 := b5e713 (k y x) y
               grind)
            | exact resolve b5e181186 b5e713
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e713 b5e181186
          have b5e187548 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e187365
               have i₂ := b5e111666
               grind)
            | exact superpose b5e111666 b5e187365
            | exact resolve b5e187365 b5e111666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e111666 b5e187365
          have b5e187549 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b5e187548
          have b5e187586 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e76 (σ y) (σ x)
               have i₂ := b5e187549
               grind)
            | exact superpose b5e187549 b5e76
            | exact resolve b5e76 b5e187549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76 b5e187549
          have b5e187869 : False := by grind
          exact b5e187869
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
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
        have b6e74 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
        have b6e87 : x = (M.op x y) ∨ y = (M.op x x) := by grind
        clear b6e74
        have b6e90 : y = (M.op x x) := by
          first
          | (have r₁ := b6e87
             have r₂ := b6e21
             grind)
          | exact resolve b6e87 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e93 : False := by grind
        exact b6e93
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b7e29 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
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
          have b7e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e33 X0 (M.op (M.op x x) X0) X1
               have i₂ := b7e33 x x X0
               grind)
            | exact superpose b7e33 b7e33
            | exact resolve b7e33 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e41 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e41
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
          have b7e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b7e71 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
          have b7e72 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e21
               grind)
            | exact resolve b7e71 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e74 : y = (M.op x y) := by
            first
            | (have r₁ := b7e72
               have r₂ := b7e22
               grind)
            | exact resolve b7e72 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e83 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e26
            | exact resolve b7e26 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e87 : ∀ X0 : G, (M.op X0 (M.op (M.op y X0) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y x
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e13
            | exact resolve b7e13 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e114 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (M.op X0 (σ x))) = (k (σ y) (M.op (σ x) (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have i₁ := b7e17 (σ y) (M.op (σ x) (M.op X0 (σ x)))
               have i₂ := b7e29 X0
               grind)
            | exact superpose b7e29 b7e17
            | (have j0 := b7e17 (σ y) (M.op (σ x) (M.op X0 (σ x)))
               grind)
            | (have r₁ := b7e17 (σ y) (M.op (σ x) (M.op X0 (σ x)))
               have r₂ := b7e29 X0
               grind)
            | exact resolve b7e17 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e118 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (M.op X0 (σ x))) = (k (σ y) (M.op (σ x) (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have j0 := b7e114 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e114
          have b7e121 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (M.op X0 (σ x))) = (k (σ y) (M.op (σ x) (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have i₁ := b7e118 X0
               have i₂ := b7e36 X0 (σ x)
               grind)
            | exact superpose b7e36 b7e118
            | (have j0 := b7e118 X0
               grind)
            | exact resolve b7e118 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118
          have b7e124 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e121 x
               have i₂ := b7e36 x (σ x)
               grind)
            | exact superpose b7e36 b7e121
            | exact resolve b7e121 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e121
          have b7e125 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e124
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e124
            | exact resolve b7e124 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e124
          have b7e132 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e36 X1 X1
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e36 X0 X1
               have i₂ := b7e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b7e18 b7e36
            | (have j1 := b7e18 X1 X0
               grind)
            | exact resolve b7e36 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e133 : y = (M.op y y) := by
            first
            | (have i₁ := b7e36 x y
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e36
            | exact resolve b7e36 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e142 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e132 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e132
          have b7e200 : y = (k y y) := by grind
          clear b7e133
          have b7e1720 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e57 y y
               have i₂ := b7e125
               grind)
            | exact superpose b7e125 b7e57
            | exact resolve b7e57 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57 b7e125
          have b7e1746 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
          clear b7e1720
          have b7e1754 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have r₁ := b7e1746
               have r₂ := b7e83
               grind)
            | exact resolve b7e1746 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1746
          have b7e1757 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e1754
               have i₂ := b7e200
               grind)
            | exact superpose b7e200 b7e1754
            | exact resolve b7e1754 b7e200
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e200 b7e1754
          have b7e1759 : (σ x) = (σ (k y x)) := by
            first
            | (have r₁ := b7e1757
               have r₂ := b7e83
               grind)
            | exact resolve b7e1757 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83 b7e1757
          have b7e1765 : (k y x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e1759
               grind)
            | exact superpose b7e1759 b7e14
            | exact resolve b7e14 b7e1759
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1759
          have b7e1795 : x = (k y x) := by
            first
            | (have i₁ := b7e1765
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1765
            | exact resolve b7e1765 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1765
          have b7e1928 : y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e142 x y
               have i₂ := b7e1795
               grind)
            | exact superpose b7e1795 b7e142
            | (have j0 := b7e142 x y
               grind)
            | exact resolve b7e142 b7e1795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e142 b7e1795
          have b7e2481 : x = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e36 y x
               have i₂ := b7e1928
               grind)
            | exact superpose b7e1928 b7e36
            | exact resolve b7e36 b7e1928
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e1928
          have b7e2499 : x = (M.op y x) := by
            first
            | (have r₁ := b7e2481
               have r₂ := b7e22
               grind)
            | exact resolve b7e2481 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2481
          have b7e2772 : x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b7e87 x
               have i₂ := b7e2499
               grind)
            | exact superpose b7e2499 b7e87
            | exact resolve b7e87 b7e2499
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87 b7e2499
          have b7e2804 : x = (M.op x y) := by
            first
            | (have i₁ := b7e2772
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e2772
            | exact resolve b7e2772 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74 b7e2772
          have b7e2806 : False := by grind
          exact b7e2806
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e398 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          have b8e459 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e398
               have r₂ := b8e23
               grind)
            | exact resolve b8e398 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e398
          have b8e464 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e459
               have r₂ := b8e24
               grind)
            | exact resolve b8e459 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e459
          have b8e465 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e464
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e464
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e464 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e464
          have b8e466 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e465
          have b8e467 : x = (M.op x y) := by
            first
            | (have r₁ := b8e466
               have r₂ := b8e21
               grind)
            | exact resolve b8e466 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e466
          have b8e468 : False := by grind
          exact b8e468

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation947 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law947 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
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
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ y) (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
               have i₂ := b4e13 X0 X1 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : x = (M.op y (M.op y y)) := by
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
          have b4e86 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) := by
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
          have b4e91 : (σ x) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b4e86
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e86
            | exact resolve b4e86 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e86
          have b4e142 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e34 X0 X2 X2 X1
               have i₂ := b4e13 X0 X2 X1
               grind)
            | exact superpose b4e13 b4e34
            | exact resolve b4e34 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e200 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) X2
               have i₂ := b4e37 X1 (M.op X2 X1) X3 X0
               grind)
            | exact superpose b4e37 b4e13
            | exact resolve b4e13 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e205 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X2 X1) (M.op X1 X1))) (M.op (M.op X2 X1) (M.op X1 X1))) = X1 := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e200 X1 x X2 X3
               have i₂ := b4e142 x X1 (M.op X2 x)
               grind)
            | exact superpose b4e142 b4e200
            | exact resolve b4e200 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e200
          have b4e219 : ∀ X1 X3 : G, (M.op (M.op X3 (M.op X1 (M.op X1 X1))) (M.op X1 (M.op X1 X1))) = X1 := by
            intro X1 X3
            first
            | (have i₁ := b4e205 x X1 X3
               have i₂ := b4e142 x X1 x
               grind)
            | exact superpose b4e142 b4e205
            | exact resolve b4e205 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e205
          have b4e365 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op y y))) (σ x)) = (M.op (σ y) (M.op (σ (M.op y y)) (σ (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b4e142 (σ (M.op y y)) X0 (σ y)
               have i₂ := b4e91
               grind)
            | exact superpose b4e91 b4e142
            | exact resolve b4e142 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e374 : ∀ X0 : G, (M.op (M.op X0 (M.op y y)) x) = (M.op y (M.op (M.op y y) (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b4e142 (M.op y y) X0 y
               have i₂ := b4e38
               grind)
            | exact superpose b4e38 b4e142
            | exact resolve b4e142 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e379 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 x
               have i₂ := b4e142 X1 x X0
               grind)
            | exact superpose b4e142 b4e13
            | exact resolve b4e13 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e395 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y y)) x) := by
            intro X0
            first
            | (have i₁ := b4e374 X0
               have i₂ := b4e13 y y y
               grind)
            | exact superpose b4e13 b4e374
            | exact resolve b4e374 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e374
          have b4e401 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op y y))) (σ x)) = (M.op (σ y) (σ (M.op (M.op y y) (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b4e365 X0
               have i₂ := b4e30 (M.op y y)
               grind)
            | exact superpose b4e30 b4e365
            | exact resolve b4e365 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e365
          have b4e432 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op y y))) (σ x)) = (M.op (σ y) (σ (M.op y (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b4e401 X0
               have i₂ := b4e142 y y y
               grind)
            | exact superpose b4e142 b4e401
            | exact resolve b4e401 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e401
          have b4e452 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (σ (M.op y y))) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e432 X0
               have i₂ := b4e38
               grind)
            | exact superpose b4e38 b4e432
            | exact resolve b4e432 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e432
          have b4e464 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op y y))) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e452 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e452
            | exact resolve b4e452 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e452
          have b4e486 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 X1 X1 X0 X0
               have i₂ := b4e379 X1 (M.op X0 X1)
               grind)
            | exact superpose b4e379 b4e34
            | exact resolve b4e34 b4e379
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e505 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e486 X0 X1
               have i₂ := b4e142 X1 X0 X0
               grind)
            | exact superpose b4e142 b4e486
            | exact resolve b4e486 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e486
          have b4e568 : y = (M.op x x) := by
            first
            | (have i₁ := b4e395 y
               have i₂ := b4e38
               grind)
            | exact superpose b4e38 b4e395
            | exact resolve b4e395 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e578 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X1 (M.op y y)) (M.op x x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e142 x X0 (M.op X1 (M.op y y))
               have i₂ := b4e395 X1
               grind)
            | exact superpose b4e395 b4e142
            | exact resolve b4e142 b4e395
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e580 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op x (M.op (M.op X1 (M.op y y)) x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e578 X0 X1
               have i₂ := b4e505 (M.op X1 (M.op y y)) x
               grind)
            | exact superpose b4e505 b4e578
            | exact resolve b4e578 b4e505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e578
          have b4e584 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) y) := by
            intro X0
            first
            | (have i₁ := b4e580 X0 x
               have i₂ := b4e395 x
               grind)
            | exact superpose b4e395 b4e580
            | exact resolve b4e580 b4e395
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e395 b4e580
          have b4e601 : ∀ X0 : G, x = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e379 X0 x
               have i₂ := b4e568
               grind)
            | exact superpose b4e568 b4e379
            | exact resolve b4e379 b4e568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e568
          have b4e652 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e142 y X0 (M.op X0 y)
               have i₂ := b4e601 (M.op X0 y)
               grind)
            | exact superpose b4e601 b4e142
            | exact resolve b4e142 b4e601
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142 b4e601
          have b4e657 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 y) y)) := by
            intro X0
            first
            | (have i₁ := b4e652 X0
               have i₂ := b4e505 (M.op X0 y) y
               grind)
            | exact superpose b4e505 b4e652
            | exact resolve b4e652 b4e505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e652
          have b4e925 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e584 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e584
            | exact resolve b4e584 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e584
          have b4e1043 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e219 (M.op X1 X1) x
               have i₂ := b4e379 (M.op X1 X1) X1
               grind)
            | exact superpose b4e379 b4e219
            | exact resolve b4e219 b4e379
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e219 b4e379
          have b4e1218 : (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b4e1043 (σ (M.op y y)) (σ y)
               have i₂ := b4e91
               grind)
            | exact superpose b4e91 b4e1043
            | exact resolve b4e1043 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91 b4e1043
          have b4e1290 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b4e1218
               have i₂ := b4e30 (M.op y y)
               grind)
            | exact superpose b4e30 b4e1218
            | exact resolve b4e1218 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e1218
          have b4e1321 : (σ (M.op y (M.op (M.op y y) y))) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b4e1290
               have i₂ := b4e505 (M.op y y) y
               grind)
            | exact superpose b4e505 b4e1290
            | exact resolve b4e1290 b4e505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e505 b4e1290
          have b4e1342 : (σ x) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b4e1321
               have i₂ := b4e657 y
               grind)
            | exact superpose b4e657 b4e1321
            | exact resolve b4e1321 b4e657
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e657 b4e1321
          have b4e2106 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ x) (M.op (M.op X0 (σ (M.op y y))) (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ (M.op y y)) (σ x) X0
               have i₂ := b4e1342
               grind)
            | exact superpose b4e1342 b4e13
            | exact resolve b4e13 b4e1342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1342
          have b4e2121 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e2106 x
               have i₂ := b4e464 x
               grind)
            | exact superpose b4e464 b4e2106
            | exact resolve b4e2106 b4e464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e464 b4e2106
          have b4e2220 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e2121
               grind)
            | exact superpose b4e2121 b4e20
            | exact resolve b4e20 b4e2121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2121
          have b4e2244 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e2220
               have i₂ := b4e925
               grind)
            | exact superpose b4e925 b4e2220
            | exact resolve b4e2220 b4e925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e925 b4e2220
          have b4e2245 : False := by grind
          exact b4e2245
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
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
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e32 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : x = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b5e32 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e32
            | exact resolve b5e32 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e94 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 X0 X2 X2 X1
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e33
            | exact resolve b5e33 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e276 : ∀ X0 : G, (M.op (M.op X0 (M.op y y)) x) = (M.op y (M.op (M.op y y) (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b5e94 (M.op y y) X0 y
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e94
            | exact resolve b5e94 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e281 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 x
               have i₂ := b5e94 X1 x X0
               grind)
            | exact superpose b5e94 b5e13
            | exact resolve b5e13 b5e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94
          have b5e297 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y y)) x) := by
            intro X0
            first
            | (have i₁ := b5e276 X0
               have i₂ := b5e13 y y y
               grind)
            | exact superpose b5e13 b5e276
            | exact resolve b5e276 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e276
          have b5e348 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e281 X1 (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e281
            | exact resolve b5e281 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e428 : y = (M.op x x) := by
            first
            | (have i₁ := b5e297 y
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e297
            | exact resolve b5e297 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e297
          have b5e3090 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e348 x X0
               have i₂ := b5e428
               grind)
            | exact superpose b5e428 b5e348
            | exact resolve b5e348 b5e428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e348 b5e428
          have b5e3262 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e281 (σ y) (σ y)
               have i₂ := b5e3090 (σ y)
               grind)
            | exact superpose b5e3090 b5e281
            | exact resolve b5e281 b5e3090
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e281 b5e3090
          have b5e3291 : False := by grind
          exact b5e3291
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
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
          have b7e32 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ y) (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
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
          have b7e45 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e46 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e47 : (σ x) = (σ (k x y)) := by
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
          have b7e50 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e14
            | exact resolve b7e14 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e51 : x = (k x y) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e50
            | exact resolve b7e50 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e62 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e22
               grind)
            | exact resolve b7e61 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e64 : x = (M.op x y) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e21
               grind)
            | exact resolve b7e62 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e80 : ∀ X0 : G, y = (M.op X0 (M.op x (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 x
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e13
            | exact resolve b7e13 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e92 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b7e32 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e97 : (σ x) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b7e92
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e92
            | exact resolve b7e92 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e92
          have b7e132 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e33 X0 X2 X2 X1
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e33
            | exact resolve b7e33 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e384 : ∀ X0 X1 : G, (M.op y (M.op X1 (M.op x (M.op X0 y)))) = (M.op X1 (M.op (M.op x (M.op X0 y)) (M.op x (M.op X0 y)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e132 (M.op x (M.op X0 y)) X0 X1
               have i₂ := b7e80 X0
               grind)
            | exact superpose b7e80 b7e132
            | exact resolve b7e132 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e420 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 x
               have i₂ := b7e132 X1 x X0
               grind)
            | exact superpose b7e132 b7e13
            | exact resolve b7e13 b7e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e461 : ∀ X0 X1 : G, (M.op y (M.op X1 (M.op x (M.op X0 y)))) = (M.op X1 (M.op x (M.op (M.op X0 y) (M.op X0 y)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e384 X0 X1
               have i₂ := b7e132 (M.op X0 y) x x
               grind)
            | exact superpose b7e132 b7e384
            | exact resolve b7e384 b7e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e384
          have b7e486 : ∀ X0 X1 : G, (M.op y (M.op X1 (M.op x (M.op X0 y)))) = (M.op X1 (M.op x (M.op X0 (M.op y y)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e461 X0 X1
               have i₂ := b7e132 y X0 X0
               grind)
            | exact superpose b7e132 b7e461
            | exact resolve b7e461 b7e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e461
          have b7e514 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e420 X2 (M.op X0 X1)
               have i₂ := b7e132 X1 X0 X0
               grind)
            | exact superpose b7e132 b7e420
            | exact resolve b7e420 b7e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e517 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b7e420 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b7e420 (M.op X0 X0) X0
               grind)
            | exact superpose b7e420 b7e420
            | exact resolve b7e420 b7e420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e522 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 X1 X1 X0 X0
               have i₂ := b7e420 X1 (M.op X0 X1)
               grind)
            | exact superpose b7e420 b7e33
            | exact resolve b7e33 b7e420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e530 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) = (M.op X2 (M.op (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e132 (M.op X2 (M.op X0 X0)) X1 X2
               have i₂ := b7e420 X2 X0
               grind)
            | exact superpose b7e420 b7e132
            | exact resolve b7e132 b7e420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e531 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op X2 (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e132 (M.op X1 (M.op X0 X0)) X1 X2
               have i₂ := b7e420 X1 X0
               grind)
            | exact superpose b7e420 b7e132
            | exact resolve b7e132 b7e420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e535 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
               have i₂ := b7e420 (M.op X1 (M.op X0 X0)) X0
               grind)
            | exact superpose b7e420 b7e13
            | exact resolve b7e13 b7e420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e420
          have b7e538 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op X2 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e531 X0 X1 X2
               have i₂ := b7e132 (M.op X0 X0) X1 X1
               grind)
            | exact superpose b7e132 b7e531
            | exact resolve b7e531 b7e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e531
          have b7e539 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e530 X0 X1 X2
               have i₂ := b7e13 (M.op X0 X0) X2 X2
               grind)
            | exact superpose b7e13 b7e530
            | exact resolve b7e530 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e530
          have b7e541 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e522 X0 X1
               have i₂ := b7e132 X1 X0 X0
               grind)
            | exact superpose b7e132 b7e522
            | exact resolve b7e522 b7e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e522
          have b7e544 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e538 X0 X1 X2
               have i₂ := b7e132 X0 X0 X0
               grind)
            | exact superpose b7e132 b7e538
            | exact resolve b7e538 b7e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e538
          have b7e627 : y = (M.op (M.op y y) (M.op x (M.op y y))) := by
            first
            | (have i₁ := b7e80 (M.op y y)
               have i₂ := b7e517 y
               grind)
            | exact superpose b7e517 b7e80
            | exact resolve b7e80 b7e517
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e630 : y = (M.op x (M.op (M.op y y) (M.op y y))) := by
            first
            | (have i₁ := b7e627
               have i₂ := b7e541 x (M.op y y)
               grind)
            | exact superpose b7e541 b7e627
            | exact resolve b7e627 b7e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e627
          have b7e638 : y = (M.op x (M.op y (M.op (M.op y y) y))) := by
            first
            | (have i₁ := b7e630
               have i₂ := b7e541 (M.op y y) y
               grind)
            | exact superpose b7e541 b7e630
            | exact resolve b7e630 b7e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e541 b7e630
          have b7e645 : y = (M.op x (M.op y (M.op y y))) := by
            first
            | (have i₁ := b7e638
               have i₂ := b7e517 y
               grind)
            | exact superpose b7e517 b7e638
            | exact resolve b7e638 b7e517
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e517 b7e638
          have b7e702 : ∀ X0 : G, (M.op (M.op X0 (M.op y (M.op y y))) y) = (M.op x (M.op (M.op y (M.op y y)) (M.op y (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b7e132 (M.op y (M.op y y)) X0 x
               have i₂ := b7e645
               grind)
            | exact superpose b7e645 b7e132
            | exact resolve b7e132 b7e645
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e132 b7e645
          have b7e705 : ∀ X0 : G, (M.op (M.op X0 (M.op y (M.op y y))) y) = (M.op y (M.op x (M.op (M.op y (M.op y y)) (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b7e702 X0
               have i₂ := b7e544 y (M.op y (M.op y y)) x
               grind)
            | exact superpose b7e544 b7e702
            | exact resolve b7e702 b7e544
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e544 b7e702
          have b7e710 : ∀ X0 : G, (M.op (M.op X0 (M.op y (M.op y y))) y) = (M.op y (M.op y (M.op x (M.op (M.op y (M.op y y)) y)))) := by
            intro X0
            first
            | (have i₁ := b7e705 X0
               have i₂ := b7e486 (M.op y (M.op y y)) y
               grind)
            | exact superpose b7e486 b7e705
            | exact resolve b7e705 b7e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e486 b7e705
          have b7e712 : ∀ X0 : G, (M.op (M.op X0 (M.op y (M.op y y))) y) = (M.op y (M.op y (M.op x (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b7e710 X0
               have i₂ := b7e535 y y
               grind)
            | exact superpose b7e535 b7e710
            | exact resolve b7e710 b7e535
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e535 b7e710
          have b7e714 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op y (M.op y y))) y) := by
            intro X0
            first
            | (have i₁ := b7e712 X0
               have i₂ := b7e514 x y y
               grind)
            | exact superpose b7e514 b7e712
            | exact resolve b7e712 b7e514
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e514 b7e712
          have b7e716 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e714 x
               have i₂ := b7e539 y x y
               grind)
            | exact superpose b7e539 b7e714
            | exact resolve b7e714 b7e539
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e539 b7e714
          have b7e718 : x = (M.op y y) := by
            first
            | (have i₁ := b7e716
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e716
            | exact resolve b7e716 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e716
          have b7e756 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e97
               have i₂ := b7e718
               grind)
            | exact superpose b7e718 b7e97
            | exact resolve b7e97 b7e718
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97 b7e718
          have b7e772 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e756
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e756
            | exact resolve b7e756 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e756
          have b7e774 : False := by grind
          exact b7e774
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
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e157 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
          have b8e182 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e157
               have r₂ := b8e24
               grind)
            | exact resolve b8e157 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157
          have b8e191 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e182
               have r₂ := b8e23
               grind)
            | exact resolve b8e182 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e182
          have b8e196 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e191
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e191
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e191
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e191
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e191 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e191
          have b8e197 : y = (M.op y x) ∨ x = y := by grind
          clear b8e196
          have b8e198 : x = y := by
            first
            | (have r₁ := b8e197
               have r₂ := b8e22
               grind)
            | exact resolve b8e197 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e197
          have b8e199 : False := by grind
          exact b8e199

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
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
          have b4e33 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e32 (M.op y y)
               have i₂ := b4e13 y y y
               grind)
            | exact superpose b4e13 b4e32
            | exact resolve b4e32 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e94 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e33 (M.op (σ y) (σ y))
               have i₂ := b4e13 (σ y) (σ y) (σ y)
               grind)
            | exact superpose b4e13 b4e33
            | exact resolve b4e33 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e97 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e94
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e94
            | exact resolve b4e94 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e94
          have b4e258 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e97
               grind)
            | exact superpose b4e97 b4e20
            | exact resolve b4e20 b4e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e97
          have b4e268 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e258
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e258
            | exact resolve b4e258 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e258
          have b4e269 : False := by grind
          exact b4e269
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e32 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
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
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
               have i₂ := b5e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b5e32 (M.op y y)
               have i₂ := b5e13 y y y
               grind)
            | exact superpose b5e13 b5e32
            | exact resolve b5e32 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op y (M.op X0 X0)) x
               have i₂ := b5e32 X0
               grind)
            | exact superpose b5e32 b5e13
            | exact resolve b5e13 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e90 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e34 (σ X0) (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e34
            | exact resolve b5e34 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e94 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 X0 X0
               have i₂ := b5e34 X0 X0
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e96 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op x (M.op y (M.op X0 (M.op X1 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 (M.op X1 X0)
               have i₂ := b5e34 X1 X0
               grind)
            | exact superpose b5e34 b5e32
            | exact resolve b5e32 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e98 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e90 X0
               have i₂ := b5e30 (M.op X0 X0)
               grind)
            | exact superpose b5e30 b5e90
            | exact resolve b5e90 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e90
          have b5e99 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e98 X0
               have i₂ := b5e34 X0 X0
               grind)
            | exact superpose b5e34 b5e98
            | exact resolve b5e98 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e98
          have b5e132 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e13 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
               have i₂ := b5e33 X1 x x X0
               grind)
            | exact superpose b5e33 b5e13
            | exact resolve b5e13 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e609 : ∀ X0 : G, (M.op (M.op X0 y) (M.op X0 y)) = (M.op x (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e96 (M.op X0 y) (M.op X0 y)
               have i₂ := b5e13 (M.op X0 y) y X0
               grind)
            | exact superpose b5e13 b5e96
            | exact resolve b5e96 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96
          have b5e618 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e609 X0
               have i₂ := b5e34 X0 y
               grind)
            | exact superpose b5e34 b5e609
            | exact resolve b5e609 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e609
          have b5e693 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e32 (M.op X0 (M.op X0 X0))
               have i₂ := b5e132 X0 X0 X0
               grind)
            | exact superpose b5e132 b5e32
            | exact resolve b5e32 b5e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e132
          have b5e745 : ∀ X0 : G, (M.op X0 (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e94 X0
               have i₂ := b5e693 X0
               grind)
            | exact superpose b5e693 b5e94
            | exact resolve b5e94 b5e693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94 b5e693
          have b5e835 : x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b5e745 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e745
            | exact resolve b5e745 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e745
          have b5e858 : x = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b5e835
               have i₂ := b5e618 x
               grind)
            | exact superpose b5e618 b5e835
            | exact resolve b5e835 b5e618
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e618 b5e835
          have b5e859 : x = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b5e858
               have i₂ := b5e35
               grind)
            | exact superpose b5e35 b5e858
            | exact resolve b5e858 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e858
          have b5e894 : y = (M.op x x) := by
            first
            | (have i₁ := b5e36 y y
               have i₂ := b5e859
               grind)
            | exact superpose b5e859 b5e36
            | exact resolve b5e36 b5e859
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e859
          have b5e950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e99 x
               have i₂ := b5e894
               grind)
            | exact superpose b5e894 b5e99
            | exact resolve b5e99 b5e894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99 b5e894
          have b5e965 : False := by grind
          exact b5e965
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e32 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 := by
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
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
               have i₂ := b7e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b7e26
          have b7e40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e36 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e36
            | exact resolve b7e36 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e41 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b7e40
          have b7e42 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e45 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e23
               grind)
            | exact resolve b7e44 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e46 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e45
            | exact resolve b7e45 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e14
            | exact resolve b7e14 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e50 : x = (k x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e49
            | exact resolve b7e49 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e56 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e46
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e46 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e57 : (σ (M.op x y)) = (σ x) ∨ x = y := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e22
               grind)
            | exact resolve b7e56 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e58 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e21
               grind)
            | exact resolve b7e57 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e60 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e22
               grind)
            | exact resolve b7e60 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e63 : x = (M.op x y) := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e21
               grind)
            | exact resolve b7e61 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e78 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y x
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e13
            | exact resolve b7e13 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e91 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e32 (M.op (σ y) (σ y))
               have i₂ := b7e13 (σ y) (σ y) (σ y)
               grind)
            | exact superpose b7e13 b7e32
            | exact resolve b7e32 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e94 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e91
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e91
            | exact resolve b7e91 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e108 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e34 (σ X0) (σ X0)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e34
            | exact resolve b7e34 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e110 : (M.op y x) = (M.op x x) := by
            first
            | (have i₁ := b7e34 x y
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e34
            | exact resolve b7e34 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e115 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e108 X0
               have i₂ := b7e30 (M.op X0 X0)
               grind)
            | exact superpose b7e30 b7e108
            | exact resolve b7e108 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e117 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e115 X0
               have i₂ := b7e34 X0 X0
               grind)
            | exact superpose b7e34 b7e115
            | exact resolve b7e115 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e115
          have b7e121 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) (M.op y x))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 x X0 X1
               have i₂ := b7e110
               grind)
            | exact superpose b7e110 b7e13
            | exact resolve b7e13 b7e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e149 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e13 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
               have i₂ := b7e33 X1 x x X0
               grind)
            | exact superpose b7e33 b7e13
            | exact resolve b7e13 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e150 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ x) (M.op (σ y) (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e32 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
               have i₂ := b7e33 (M.op X0 X1) X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b7e33 b7e32
            | exact resolve b7e32 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e153 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e150 X0 X1
               have i₂ := b7e34 X0 X1
               grind)
            | exact superpose b7e34 b7e150
            | exact resolve b7e150 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150
          have b7e256 : ∀ X0 : G, (σ X0) = (M.op y (M.op x (σ (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b7e78 (σ X0)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e78
            | exact resolve b7e78 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e78
          have b7e336 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
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
          have b7e346 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e336
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e336
            | exact resolve b7e336 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58 b7e336
          have b7e654 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) = (M.op y (M.op x (σ (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e256 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
               have i₂ := b7e33 (M.op X0 X1) X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b7e33 b7e256
            | exact resolve b7e256 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e670 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op y (M.op x (σ (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e654 X0 X1
               have i₂ := b7e34 X0 X1
               grind)
            | exact superpose b7e34 b7e654
            | exact resolve b7e654 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e654
          have b7e672 : ∀ X0 X1 : G, (σ (M.op (σ x) (M.op (σ y) (M.op X0 X1)))) = (M.op y (M.op x (σ (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e670 X0 X1
               have i₂ := b7e153 X0 X1
               grind)
            | exact superpose b7e153 b7e670
            | exact resolve b7e670 b7e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e670
          have b7e728 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op y (M.op x (σ X0))) := by
            intro X0
            first
            | (have i₁ := b7e256 (M.op X0 (M.op X0 X0))
               have i₂ := b7e149 X0 X0 X0
               grind)
            | exact superpose b7e149 b7e256
            | exact resolve b7e256 b7e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e149
          have b7e909 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) = (M.op (M.op X0 X0) (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) := by
            intro X0
            first
            | (have i₁ := b7e117 (M.op (τ X0) (τ X0))
               have i₂ := b7e41 X0
               grind)
            | exact superpose b7e41 b7e117
            | exact resolve b7e117 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41 b7e117
          have b7e939 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (M.op (τ X0) (τ X0))))) = (M.op (M.op X0 X0) (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
            intro X0
            first
            | (have i₁ := b7e909 X0
               have i₂ := b7e34 (τ X0) (τ X0)
               grind)
            | exact superpose b7e34 b7e909
            | exact resolve b7e909 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e909
          have b7e954 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (M.op (τ X0) (τ X0))))) = (M.op (M.op X0 X0) (M.op y (M.op x (σ (τ X0))))) := by
            intro X0
            first
            | (have i₁ := b7e939 X0
               have i₂ := b7e728 (τ X0)
               grind)
            | exact superpose b7e728 b7e939
            | exact resolve b7e939 b7e728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e728 b7e939
          have b7e964 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (M.op (τ X0) (τ X0))))) = (M.op (M.op X0 X0) (M.op y (M.op x X0))) := by
            intro X0
            first
            | (have i₁ := b7e954 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e954
            | exact resolve b7e954 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e954
          have b7e972 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op y (M.op x X0))) = (σ (M.op (σ x) (M.op (σ y) (M.op (τ X0) (τ X0))))) := by
            intro X0
            first
            | (have i₁ := b7e964 X0
               have i₂ := b7e153 (τ X0) (τ X0)
               grind)
            | exact superpose b7e153 b7e964
            | exact resolve b7e964 b7e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e153 b7e964
          have b7e974 : ∀ X0 : G, (M.op y (M.op x (σ (M.op (τ X0) (τ X0))))) = (M.op (M.op X0 X0) (M.op y (M.op x X0))) := by
            intro X0
            first
            | (have i₁ := b7e972 X0
               have i₂ := b7e672 (τ X0) (τ X0)
               grind)
            | exact superpose b7e672 b7e972
            | exact resolve b7e972 b7e672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e672 b7e972
          have b7e975 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op y (M.op x X0))) := by
            intro X0
            first
            | (have i₁ := b7e974 X0
               have i₂ := b7e256 (τ X0)
               grind)
            | exact superpose b7e256 b7e974
            | exact resolve b7e974 b7e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e256 b7e974
          have b7e976 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op y (M.op x X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e975 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e975
            | exact resolve b7e975 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e975
          have b7e984 : y = (M.op (M.op y y) (M.op y x)) := by
            first
            | (have i₁ := b7e976 y
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e976
            | exact resolve b7e976 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63 b7e976
          have b7e1047 : x = (M.op y y) := by
            first
            | (have i₁ := b7e121 y y
               have i₂ := b7e984
               grind)
            | exact superpose b7e984 b7e121
            | exact resolve b7e121 b7e984
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e121 b7e984
          have b7e1098 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b7e346
               have i₂ := b7e1047
               grind)
            | exact superpose b7e1047 b7e346
            | exact resolve b7e346 b7e1047
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e346 b7e1047
          have b7e1127 : False := by grind
          exact b7e1127
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
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e138 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
          have b8e159 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e138
               have r₂ := b8e24
               grind)
            | exact resolve b8e138 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138
          have b8e164 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e159
               have r₂ := b8e23
               grind)
            | exact resolve b8e159 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e159
          have b8e165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e164
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e164
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e164
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e164
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e164 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e164
          have b8e166 : y = (M.op y x) ∨ x = y := by grind
          clear b8e165
          have b8e167 : x = y := by
            first
            | (have r₁ := b8e166
               have r₂ := b8e22
               grind)
            | exact resolve b8e166 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e166
          have b8e168 : False := by grind
          exact b8e168
