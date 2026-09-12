import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3718`: `x ◇ y = (x ◇ x) ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_x_x_pyx_Equation3718 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3718 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3718.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x y) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (σ x) ≠ (σ x) := by
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
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e38 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 (M.op X3 X1) (M.op X0 X0)
             have i₂ := b1e12 X0 X1 X3
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
          intro X1 X2 X3
          first
          | (have i₁ := b1e40 x X1 X2 X3
             have i₂ := b1e12 X2 X1 x
             grind)
          | exact superpose b1e12 b1e40
          | exact resolve b1e40 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e54 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X1 X1) (M.op X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 x (M.op X0 X0)
             have i₂ := b1e38 X0
             grind)
          | exact superpose b1e38 b1e12
          | exact resolve b1e12 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e56 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b1e54 x X1
             have i₂ := b1e12 X1 y x
             grind)
          | exact superpose b1e12 b1e54
          | exact resolve b1e54 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e17 (σ X1) (σ X0)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X1)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : x = (M.op x x) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e56 x
             grind)
          | exact superpose b1e56 b1e20
          | exact resolve b1e20 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e81 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e42 (σ x) X0 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e42
          | exact resolve b1e42 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e101 : x ≠ x ∨ x = (k x x) := by
          first
          | (have i₁ := b1e15 x x
             have i₂ := b1e73
             grind)
          | exact superpose b1e73 b1e15
          | (have j0 := b1e15 x x
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e73
             grind)
          | exact resolve b1e15 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e102 : x = (k x x) := by grind
        clear b1e101
        have b1e143 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e81 (σ x)
             grind)
          | exact superpose b1e81 b1e21
          | exact resolve b1e21 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81
        have b1e302 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e63 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e304 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e302 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e302
        have b1e1075 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e304 x
             have i₂ := b1e102
             grind)
          | exact superpose b1e102 b1e304
          | (have j0 := b1e304 x
             grind)
          | exact resolve b1e304 b1e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102 b1e304
        have b1e1082 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e1075
        have b1e1090 : False := by grind
        exact b1e1090
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
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
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x ≠ x ∨ x = (k x y) := by
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
        have b2e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 X1)) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (M.op X0 X0) X1 X2
             have i₂ := b2e12 X0 X0 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 (M.op X3 X1) (M.op X0 X0)
             have i₂ := b2e12 X0 X1 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
          intro X1 X2 X3
          first
          | (have i₁ := b2e34 x X1 X2 X3
             have i₂ := b2e12 X2 X1 x
             grind)
          | exact superpose b2e12 b2e34
          | exact resolve b2e34 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e37 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X0 X1 x
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e32
          | exact resolve b2e32 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e39 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X1 X1) (M.op X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 x (M.op X0 X0)
             have i₂ := b2e33 X0
             grind)
          | exact superpose b2e33 b2e12
          | exact resolve b2e12 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b2e39 x X1
             have i₂ := b2e12 X1 y x
             grind)
          | exact superpose b2e12 b2e39
          | exact resolve b2e39 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39
        have b2e43 : x ≠ x ∨ y = (M.op y x) ∨ y = (k y x) := by
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
        have b2e44 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X0 X0)) ∨ (M.op X2 X1) = (k (M.op X2 X1) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e16 (M.op X2 X1) (M.op X0 X0)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e16
          | (have j0 := b2e16 (M.op X2 X1) (M.op X0 X0)
             grind)
          | (have r₁ := b2e16 (M.op X2 X1) (M.op X1 X1)
             have r₂ := b2e12 X1 X1 X2
             grind)
          | exact resolve b2e16 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e46 : y = (M.op y x) ∨ y = (k y x) := by grind
        clear b2e43
        have b2e48 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X2 X1) = (k (M.op X2 X1) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e44 X0 X1 X2
             have j1 := b2e15 (M.op X2 X1) (M.op X0 X0)
             grind)
          | (have r₁ := b2e44 X0 X1 X2
             have r₂ := b2e15 (M.op X2 X1) (M.op X0 X0)
             grind)
          | exact resolve b2e44 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e49 : y = (k y x) := by
          first
          | (have j1 := b2e15 y x
             grind)
          | (have r₁ := b2e46
             have r₂ := b2e15 y x
             grind)
          | exact resolve b2e46 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46
        have b2e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : (M.op y x) = (M.op (M.op y x) x) := by
          first
          | (have i₁ := b2e33 y
             have i₂ := b2e41 y
             grind)
          | exact superpose b2e41 b2e33
          | exact resolve b2e33 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e63 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y x) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 y X0 X1
             have i₂ := b2e41 y
             grind)
          | exact superpose b2e41 b2e12
          | exact resolve b2e12 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e64 : x = (M.op x x) := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e41 x
             grind)
          | exact superpose b2e41 b2e20
          | exact resolve b2e20 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e65 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y x) X0) := by
          intro X0
          first
          | (have i₁ := b2e63 X0 x
             have i₂ := b2e36 X0 (M.op y x) x
             grind)
          | exact superpose b2e36 b2e63
          | exact resolve b2e63 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e75 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X0 X1) X2 X3
             have i₂ := b2e36 X1 (M.op X0 X1) X0
             grind)
          | exact superpose b2e36 b2e12
          | exact resolve b2e12 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e76 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X2 X1) = (M.op (M.op X2 X1) X0) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e16 (M.op X2 X1) X0
             have i₂ := b2e36 X1 X0 X2
             grind)
          | exact superpose b2e36 b2e16
          | (have j0 := b2e16 (M.op X2 X1) X0
             grind)
          | exact resolve b2e16 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e78 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 (M.op X2 X1)
             have i₂ := b2e36 X1 X0 X2
             grind)
          | exact superpose b2e36 b2e15
          | (have j0 := b2e15 X0 X1
             grind)
          | exact resolve b2e15 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e81 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e76 X0 X1 X2
             have j1 := b2e15 X0 X1
             grind)
          | (have r₁ := b2e76 X1 X1 X2
             have r₂ := b2e15 (M.op X2 X1) X1
             grind)
          | exact resolve b2e76 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e82 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e75 X0 X1 X2 x
             have i₂ := b2e36 X2 (M.op (M.op X0 X1) X1) x
             grind)
          | exact superpose b2e36 b2e75
          | exact resolve b2e75 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75
        have b2e91 : x ≠ x ∨ x = (k x x) := by
          first
          | (have i₁ := b2e15 x x
             have i₂ := b2e64
             grind)
          | exact superpose b2e64 b2e15
          | (have j0 := b2e15 x x
             grind)
          | (have r₁ := b2e15 x x
             have r₂ := b2e64
             grind)
          | exact resolve b2e15 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e92 : x = (k x x) := by grind
        clear b2e91
        have b2e105 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X1 (M.op X0 X0)
             have i₂ := b2e37 X0 X1
             grind)
          | exact superpose b2e37 b2e16
          | (have j0 := b2e16 X1 (M.op X0 X0)
             grind)
          | (have r₁ := b2e16 X1 (M.op X1 X1)
             have r₂ := b2e37 X1 X1
             grind)
          | exact resolve b2e16 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (M.op X0 X0) X1
             have i₂ := b2e37 X0 X1
             grind)
          | exact superpose b2e37 b2e15
          | (have j0 := b2e15 (M.op X0 X0) X1
             grind)
          | (have r₁ := b2e15 (M.op X1 X1) X1
             have r₂ := b2e37 X1 X1
             grind)
          | exact resolve b2e15 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e111 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e105 X0 X1
             have j1 := b2e15 X1 (M.op X0 X0)
             grind)
          | (have r₁ := b2e105 X0 X0
             have r₂ := b2e15 X0 (M.op X0 X0)
             grind)
          | exact resolve b2e105 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e105
        have b2e125 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e131 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (k (M.op y x) x) := by
          first
          | (have i₁ := b2e15 (M.op y x) x
             have i₂ := b2e62
             grind)
          | exact superpose b2e62 b2e15
          | (have j0 := b2e15 (M.op y x) x
             grind)
          | (have r₁ := b2e15 (M.op y x) x
             have r₂ := b2e62
             grind)
          | exact resolve b2e15 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e132 : (M.op y x) = (k (M.op y x) x) := by grind
        clear b2e131
        have b2e163 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k (M.op X0 x) x) := by
          intro X0
          first
          | (have i₁ := b2e48 x x x
             have i₂ := b2e64
             grind)
          | exact superpose b2e64 b2e48
          | exact resolve b2e48 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e173 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e48 X1 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e174 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) x) := by
          intro X0
          first
          | (have j0 := b2e163 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e163
        have b2e213 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e37 (σ X0) X1
             have i₂ := b2e54 X0 X0
             grind)
          | exact superpose b2e54 b2e37
          | (have j1 := b2e54 X0 X0
             grind)
          | exact resolve b2e37 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e222 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e54 x y
             grind)
          | exact superpose b2e54 b2e22
          | (have j1 := b2e54 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e54 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e54 y x
             grind)
          | exact resolve b2e22 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e225 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (M.op X1 (σ X2)) = (M.op X1 (σ X0)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e36 (σ X2) X1 (σ X0)
             have i₂ := b2e54 X2 X0
             grind)
          | exact superpose b2e54 b2e36
          | (have j1 := b2e54 X2 X0
             grind)
          | exact resolve b2e36 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e226 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (σ X1) (σ X0)
             have i₂ := b2e54 X1 X0
             grind)
          | exact superpose b2e54 b2e16
          | (have j0 := b2e16 (σ X1) (σ X0)
             have j1 := b2e54 X1 X0
             grind)
          | (have r₁ := b2e16 (σ X0) (σ X1)
             have r₂ := b2e54 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X1) (σ X0)
             have r₂ := b2e54 X0 X1
             grind)
          | exact resolve b2e16 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e228 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (σ X0) (σ X1)
             have i₂ := b2e54 X1 X0
             grind)
          | exact superpose b2e54 b2e15
          | (have j0 := b2e15 (σ X0) (σ X1)
             have j1 := b2e54 X1 X0
             grind)
          | (have r₁ := b2e15 (σ X1) (σ X0)
             have r₂ := b2e54 X0 X1
             grind)
          | (have r₁ := b2e15 (σ X0) (σ X1)
             have r₂ := b2e54 X0 X1
             grind)
          | exact resolve b2e15 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e229 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e54 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e231 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e229 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e229
        have b2e232 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e228 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e228
        have b2e233 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e226 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e226
        have b2e234 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e233 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e233
        have b2e235 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e222
        have b2e239 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e213 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e213
        have b2e243 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e232 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e232
          | (have j0 := b2e232 X0 X1
             grind)
          | exact resolve b2e232 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e232
        have b2e245 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e234 X0 X1
             have j1 := b2e15 (σ X1) (σ X0)
             grind)
          | (have r₁ := b2e234 X0 X1
             have r₂ := b2e15 (σ X1) (σ X0)
             grind)
          | exact resolve b2e234 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e234
        have b2e246 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e235
             have r₂ := b2e21
             grind)
          | exact resolve b2e235 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e235
        have b2e255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e245 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e245
          | (have j0 := b2e245 X0 X1
             grind)
          | exact resolve b2e245 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e245
        have b2e256 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e246
             have i₂ := b2e49
             grind)
          | exact superpose b2e49 b2e246
          | exact resolve b2e246 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e246
        have b2e259 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e256
             grind)
          | exact superpose b2e256 b2e21
          | exact resolve b2e21 b2e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e267 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e31 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e31
          | exact resolve b2e31 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e299 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 (M.op y x)) = X0 ∨ (k X0 (M.op y x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e16 X0 (M.op y x)
             have i₂ := b2e65 X0
             grind)
          | exact superpose b2e65 b2e16
          | (have j0 := b2e16 X0 (M.op y x)
             grind)
          | (have r₁ := b2e16 x (M.op y x)
             have r₂ := b2e65 x
             grind)
          | exact resolve b2e16 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e307 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k X0 (M.op y x)) = X0 := by
          intro X0
          first
          | (have j0 := b2e299 X0
             have j1 := b2e15 X0 (M.op y x)
             grind)
          | (have r₁ := b2e299 X0
             have r₂ := b2e15 X0 (M.op y x)
             grind)
          | exact resolve b2e299 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e299
        have b2e449 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) (σ X1)) X2) = (M.op (σ X0) X2) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e82 (σ X1) (σ X0) X2
             have i₂ := b2e54 X0 X1
             grind)
          | exact superpose b2e54 b2e82
          | (have j1 := b2e54 X1 X0
             grind)
          | exact resolve b2e82 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e469 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X2 (M.op (M.op X0 X1) X1)) = X2 ∨ (k X2 (M.op (M.op X0 X1) X1)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e16 X2 (M.op (M.op X0 X1) X1)
             have i₂ := b2e82 X0 X1 X2
             grind)
          | exact superpose b2e82 b2e16
          | (have j0 := b2e16 X2 (M.op (M.op X0 X1) X1)
             grind)
          | (have r₁ := b2e16 X2 (M.op (M.op X0 X2) X2)
             have r₂ := b2e82 X0 X2 X2
             grind)
          | exact resolve b2e16 b2e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e485 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X2) ∨ (k X2 (M.op (M.op X0 X1) X1)) = X2 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e469 X0 X1 X2
             have j1 := b2e15 X2 (M.op (M.op X0 X1) X1)
             grind)
          | (have r₁ := b2e469 X0 X1 X0
             have r₂ := b2e15 X0 (M.op (M.op X0 X1) X1)
             grind)
          | exact resolve b2e469 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e469
        have b2e600 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e111 x x
             have i₂ := b2e64
             grind)
          | exact superpose b2e64 b2e111
          | exact resolve b2e111 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e601 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e111 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e111
        have b2e891 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e231 x
             have i₂ := b2e92
             grind)
          | exact superpose b2e92 b2e231
          | (have j0 := b2e231 x
             grind)
          | exact resolve b2e231 b2e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92
        have b2e893 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e231 (τ X0)
             have i₂ := b2e27 X0 (τ X0)
             grind)
          | exact superpose b2e27 b2e231
          | (have j0 := b2e231 (τ X0)
             grind)
          | exact resolve b2e231 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e894 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e891
        have b2e898 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e893 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e893
          | (have j0 := b2e893 X0
             grind)
          | exact resolve b2e893 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e893
        have b2e901 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e898 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e898
          | (have j0 := b2e898 X0
             grind)
          | exact resolve b2e898 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e898
        have b2e920 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b2e78 (σ x) (σ x) X0
             have i₂ := b2e894
             grind)
          | exact superpose b2e894 b2e78
          | (have j0 := b2e78 (σ x) (σ x) X0
             grind)
          | (have r₁ := b2e78 (σ x) (σ x) x
             have r₂ := b2e894
             grind)
          | exact resolve b2e78 b2e894
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e928 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have j0 := b2e920 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e920
        have b2e974 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e901 (τ X0)
             have i₂ := b2e267 X0 X0
             grind)
          | exact superpose b2e267 b2e901
          | (have j0 := b2e901 (τ X0)
             grind)
          | exact resolve b2e901 b2e267
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e986 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (M.op (σ X0) (σ X0)) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e107 (σ X0) (σ X1)
             have i₂ := b2e54 X1 X0
             grind)
          | exact superpose b2e54 b2e107
          | (have j0 := b2e107 (σ X0) (σ X1)
             have j1 := b2e54 X1 X0
             grind)
          | exact resolve b2e107 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e107
        have b2e1012 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (M.op (σ X0) (σ X0)) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e986 X0 X1
             have j1 := b2e81 (σ X0) (σ X0) x
             grind)
          | (have r₁ := b2e986 X0 X1
             have r₂ := b2e81 (σ X1) (σ X0) x
             grind)
          | exact resolve b2e986 b2e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81 b2e986
        have b2e1057 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e255 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e255
          | exact resolve b2e255 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1089 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e36 (σ X0) X2 (σ X1)
             have i₂ := b2e255 X0 X1
             grind)
          | exact superpose b2e255 b2e36
          | (have j1 := b2e255 X0 X1
             grind)
          | exact resolve b2e36 b2e255
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e255
        have b2e1110 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e1057 X0 X1
             have i₂ := b2e27 X0 X1
             grind)
          | exact superpose b2e27 b2e1057
          | (have j0 := b2e1057 X0 X1
             grind)
          | exact resolve b2e1057 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1057
        have b2e1112 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e1110 X0 X1
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e1110
          | (have j0 := b2e1110 X0 X1
             grind)
          | exact resolve b2e1110 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1110
        have b2e1123 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b2e125 x (M.op X0 (σ x))
             have i₂ := b2e928 X0
             grind)
          | exact superpose b2e928 b2e125
          | exact resolve b2e125 b2e928
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e928
        have b2e1128 : ∀ X0 : G, x = (k x (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b2e1123 X0
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e1123
          | exact resolve b2e1123 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1123
        have b2e1141 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e239 (τ X0) X1
             have i₂ := b2e27 X0 (τ X0)
             grind)
          | exact superpose b2e27 b2e239
          | (have j0 := b2e239 (τ X0) X1
             grind)
          | exact resolve b2e239 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e239
        have b2e1193 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e1141 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1141
          | (have j0 := b2e1141 X0 X1
             grind)
          | exact resolve b2e1141 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1141
        have b2e1196 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e1193 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1193
          | (have j0 := b2e1193 X0 X1
             grind)
          | exact resolve b2e1193 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1193
        have b2e1500 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e243 (τ X0) X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e243
          | exact resolve b2e243 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e243
        have b2e1564 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e1500 X0 X1
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e1500
          | (have j0 := b2e1500 X0 X1
             grind)
          | exact resolve b2e1500 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1500
        have b2e1574 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e1564 X0 X1
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e1564
          | (have j0 := b2e1564 X0 X1
             grind)
          | exact resolve b2e1564 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1564
        have b2e1880 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (σ X2)) ∨ (σ (k X2 (τ X0))) = (M.op X0 (σ X2)) ∨ (M.op X0 (σ X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e225 X0 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e225
          | exact resolve b2e225 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1898 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (σ X2)) ∨ (σ (k (τ X0) X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (M.op (σ X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e225 (τ X0) X1 X2
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e225
          | exact resolve b2e225 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2056 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e225 X0 (σ X0) X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e225
        have b2e2097 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (M.op X1 X0) = (M.op X1 (σ X2)) ∨ (σ X2) = (M.op (σ X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e1898 X0 X1 X2
             have i₂ := b2e26 X0 X2
             grind)
          | exact superpose b2e26 b2e1898
          | (have j0 := b2e1898 X0 X1 X2
             grind)
          | exact resolve b2e1898 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1898
        have b2e2101 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (k (σ X2) X0) ∨ (M.op X1 X0) = (M.op X1 (σ X2)) ∨ (M.op X0 (σ X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e1880 X0 X1 X2
             have i₂ := b2e27 X0 X2
             grind)
          | exact superpose b2e27 b2e1880
          | (have j0 := b2e1880 X0 X1 X2
             grind)
          | exact resolve b2e1880 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1880
        have b2e4370 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e1112 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1112
          | exact resolve b2e1112 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4399 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e125 X0 (σ X1)
             have i₂ := b2e1112 (σ X0) X1
             grind)
          | exact superpose b2e1112 b2e125
          | (have j1 := b2e1112 (σ X0) X1
             grind)
          | exact resolve b2e125 b2e1112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1112
        have b2e4479 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e4399 X0 X1
             have i₂ := b2e13 X1
             grind)
          | exact superpose b2e13 b2e4399
          | (have j0 := b2e4399 X0 X1
             grind)
          | exact resolve b2e4399 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4399
        have b2e4508 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e4479 X0 X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e4479
          | (have j0 := b2e4479 X0 X1
             grind)
          | exact resolve b2e4479 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4479
        have b2e4518 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e4508 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e4508
          | (have j0 := b2e4508 X0 X1
             grind)
          | exact resolve b2e4508 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4508
        have b2e4604 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e26 X1 X0
             have i₂ := b2e4370 (τ X1) X0
             grind)
          | exact superpose b2e4370 b2e26
          | (have j1 := b2e4370 (τ X1) X0
             grind)
          | exact resolve b2e26 b2e4370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4647 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e26 X0 X1
             have i₂ := b2e4370 X1 (τ X0)
             grind)
          | exact superpose b2e4370 b2e26
          | (have j1 := b2e4370 X1 (τ X0)
             grind)
          | exact resolve b2e26 b2e4370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4370
        have b2e4666 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e4647 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e4647
          | (have j0 := b2e4647 X0 X1
             grind)
          | exact resolve b2e4647 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4647
        have b2e5329 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e1089 (τ X0) (τ X1) X2
             have i₂ := b2e267 X1 X0
             grind)
          | exact superpose b2e267 b2e1089
          | (have j0 := b2e1089 (τ X0) (τ X1) X2
             grind)
          | exact resolve b2e1089 b2e267
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e267 b2e1089
        have b2e5439 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X0))) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e5329 X0 X1 X2
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e5329
          | (have j0 := b2e5329 X0 X1 X2
             grind)
          | exact resolve b2e5329 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5329
        have b2e5445 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e5439 X0 X1 X2
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e5439
          | (have j0 := b2e5439 X0 X1 X2
             grind)
          | exact resolve b2e5439 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5439
        have b2e5446 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e5445 X0 X1 X2
             have i₂ := b2e27 X0 (τ X1)
             grind)
          | exact superpose b2e27 b2e5445
          | (have j0 := b2e5445 X0 X1 X2
             grind)
          | exact resolve b2e5445 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5445
        have b2e5447 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (k X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e5446 X0 X0 X2
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e5446
          | (have j0 := b2e5446 X0 X1 X2
             grind)
          | exact resolve b2e5446 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5446
        have b2e8123 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e974 (M.op X0 X0)
             have i₂ := b2e173 X0 X0
             grind)
          | exact superpose b2e173 b2e974
          | (have j0 := b2e974 (M.op X0 X0)
             grind)
          | exact resolve b2e974 b2e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e173 b2e974
        have b2e8143 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
          intro X0
          first
          | (have j0 := b2e8123 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8123
        have b2e12721 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e1574 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1574
          | exact resolve b2e1574 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1574
        have b2e12995 : ∀ X0 : G, (τ (σ (k X0 X0))) = (M.op (τ (σ (k X0 X0))) (τ (σ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e8143 (σ x)
             have i₂ := b2e4518 x x
             grind)
          | exact superpose b2e4518 b2e8143
          | (have j1 := b2e4518 X0 X0
             grind)
          | exact resolve b2e8143 b2e4518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8143
        have b2e13000 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (k X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e36 (σ X0) X2 (σ X1)
             have i₂ := b2e4518 X1 X0
             grind)
          | exact superpose b2e4518 b2e36
          | (have j1 := b2e4518 X1 X0
             grind)
          | exact resolve b2e36 b2e4518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4518
        have b2e13020 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12995 X0
             have i₂ := b2e13 (k X0 X0)
             grind)
          | exact superpose b2e13 b2e12995
          | (have j0 := b2e12995 X0
             grind)
          | exact resolve b2e12995 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12995
        have b2e15305 : ∀ X0 X1 : G, (k X0 (M.op X0 (σ X1))) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e601 X0
             have i₂ := b2e2101 X0 X0 X1
             grind)
          | (have i₁ := b2e601 (σ x)
             have i₂ := b2e2101 X0 (σ x) x
             grind)
          | exact superpose b2e2101 b2e601
          | (have j1 := b2e2101 X0 X1 X1
             grind)
          | exact resolve b2e601 b2e2101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e601
        have b2e15530 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e2101 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2101
        have b2e15619 : ∀ X0 X1 : G, (k X0 (M.op X0 (σ X1))) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e15305 X0 X1
             have j1 := b2e78 X0 (σ X1) X0
             grind)
          | (have r₁ := b2e15305 X0 X1
             have r₂ := b2e78 X0 (σ X1) x
             grind)
          | exact resolve b2e15305 b2e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e78 b2e15305
        have b2e17511 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e27 X0 X1
             have i₂ := b2e4666 X0 X1
             grind)
          | exact superpose b2e4666 b2e27
          | (have j1 := b2e4666 X0 X1
             grind)
          | exact resolve b2e27 b2e4666
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4666
        have b2e19876 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e894
             have i₂ := b2e2097 X0 (σ x) x
             grind)
          | (have i₁ := b2e894
             have i₂ := b2e2097 (σ x) (σ x) x
             grind)
          | exact superpose b2e2097 b2e894
          | (have j1 := b2e2097 X0 x x
             grind)
          | exact resolve b2e894 b2e2097
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e19895 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e19876 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19876
        have b2e44630 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e449 x y X0
             have i₂ := b2e256
             grind)
          | exact superpose b2e256 b2e449
          | (have j0 := b2e449 x y x
             grind)
          | exact resolve b2e449 b2e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e449
        have b2e44850 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
          intro X0
          first
          | (have j0 := b2e44630 X0
             grind)
          | (have r₁ := b2e44630 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e44630 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44630
        have b2e44884 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e44850 X0
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e44850
          | (have j0 := b2e44850 X0
             grind)
          | exact resolve b2e44850 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e44850
        have b2e50607 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e4604 X0 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e4604
          | exact resolve b2e4604 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4604
        have b2e50840 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e50607 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e50607
          | (have j0 := b2e50607 X0 X1
             grind)
          | exact resolve b2e50607 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50607
        have b2e55253 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e13000 X1 X0 X2
             have i₂ := b2e50840 X1 X0
             grind)
          | exact superpose b2e50840 b2e13000
          | (have j0 := b2e13000 X1 X0 X2
             have j1 := b2e50840 X1 X0
             grind)
          | exact resolve b2e13000 b2e50840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50840
        have b2e55484 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (M.op X0 X1))) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e55253 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55253
        have b2e56074 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e1012 x x
             have i₂ := b2e894
             grind)
          | exact superpose b2e894 b2e1012
          | (have j0 := b2e1012 x X0
             grind)
          | (have r₁ := b2e1012 x x
             have r₂ := b2e894
             grind)
          | exact resolve b2e1012 b2e894
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1012
        have b2e56093 : ∀ X0 : G, (σ x) = (k (σ x) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b2e56074 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56074
        have b2e56105 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b2e56093 X0
             have i₂ := b2e18 x X0
             grind)
          | exact superpose b2e18 b2e56093
          | (have j0 := b2e56093 X0
             grind)
          | exact resolve b2e56093 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56093
        have b2e62843 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e5447 X0 X0 (k X0 X0)
             have i₂ := b2e13020 X0
             grind)
          | exact superpose b2e13020 b2e5447
          | (have j0 := b2e5447 X0 X0 x
             have j1 := b2e13020 X0
             grind)
          | exact resolve b2e5447 b2e13020
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5447 b2e13020
        have b2e62911 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e62843 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62843
        have b2e63666 : (k y y) = (M.op (k y y) x) ∨ y = (k y y) := by
          first
          | (have i₁ := b2e41 (k y y)
             have i₂ := b2e62911 y
             grind)
          | exact superpose b2e62911 b2e41
          | (have j1 := b2e62911 y
             grind)
          | exact resolve b2e41 b2e62911
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62911
        have b2e67131 : (M.op y x) = (k y y) ∨ y = (M.op y y) ∨ y = (k y y) := by
          first
          | (have i₁ := b2e1196 y x
             have i₂ := b2e63666
             grind)
          | exact superpose b2e63666 b2e1196
          | (have j0 := b2e1196 y x
             grind)
          | exact resolve b2e1196 b2e63666
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1196 b2e63666
        have b2e67192 : (M.op y x) = (k y y) ∨ y = (M.op y y) := by
          first
          | (have j1 := b2e901 y
             grind)
          | (have r₁ := b2e67131
             have r₂ := b2e901 y
             grind)
          | exact resolve b2e67131 b2e901
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e901 b2e67131
        have b2e67193 : (M.op y x) = (k y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b2e67192
             have i₂ := b2e41 y
             grind)
          | exact superpose b2e41 b2e67192
          | exact resolve b2e67192 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67192
        have b2e68723 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y x))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b2e13000 y y x
             have i₂ := b2e67193
             grind)
          | exact superpose b2e67193 b2e13000
          | exact resolve b2e13000 b2e67193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13000 b2e67193
        have b2e68732 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y x))) ∨ y = (M.op y x) := by
          intro X0
          first
          | (have j0 := b2e68723 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68723
        have b2e72069 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e17511 (σ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e17511
          | (have j0 := b2e17511 (σ X0) X1
             grind)
          | exact resolve b2e17511 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17511
        have b2e72347 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e72069 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e72069
          | (have j0 := b2e72069 X0 X1
             grind)
          | exact resolve b2e72069 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72069
        have b2e72374 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e72347 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e72347
          | (have j0 := b2e72347 X0 X1
             grind)
          | exact resolve b2e72347 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72347
        have b2e73154 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e31 X0 x
             have i₂ := b2e19895 X0
             grind)
          | exact superpose b2e19895 b2e31
          | (have j1 := b2e19895 X0
             grind)
          | exact resolve b2e31 b2e19895
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e90015 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 x))) = (M.op X1 (σ y)) ∨ (k X0 y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e55484 X0 y X1
             have i₂ := b2e41 X0
             grind)
          | exact superpose b2e41 b2e55484
          | (have j0 := b2e55484 X0 y x
             grind)
          | exact resolve b2e55484 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55484
        have b2e106007 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e231 X0
             have i₂ := b2e72374 X0 X0
             grind)
          | exact superpose b2e72374 b2e231
          | (have j0 := b2e231 X0
             have j1 := b2e72374 X0 X0
             grind)
          | (have r₁ := b2e231 x
             have r₂ := b2e72374 x x
             grind)
          | exact resolve b2e231 b2e72374
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72374
        have b2e106429 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e106007 X0
             have j1 := b2e231 X0
             grind)
          | (have r₁ := b2e106007 X0
             have r₂ := b2e231 X0
             grind)
          | exact resolve b2e106007 b2e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e231 b2e106007
        have b2e107337 : (σ y) ≠ (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e106429 y
             have i₂ := b2e41 y
             grind)
          | exact superpose b2e41 b2e106429
          | (have j0 := b2e106429 y
             grind)
          | exact resolve b2e106429 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e106429
        have b2e192770 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e12721 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12721
        have b2e193312 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ X2 ∨ (k X2 (M.op (M.op X0 X1) X1)) = X2 ∨ (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e192770 X2 (M.op (M.op X0 X1) X1)
             have i₂ := b2e82 X0 X1 X2
             grind)
          | exact superpose b2e82 b2e192770
          | (have j0 := b2e192770 X2 (M.op X0 X1)
             grind)
          | exact resolve b2e192770 b2e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e193363 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ X2 ∨ (k X2 (M.op (M.op X0 X1) X1)) = X2 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e193312 X0 X1 X2
             have j1 := b2e485 X0 X1 X2
             grind)
          | (have r₁ := b2e193312 X0 X1 X2
             have r₂ := b2e485 X0 X1 X2
             grind)
          | (have r₁ := b2e193312 X0 X2 X2
             have r₂ := b2e485 X0 X2 X2
             grind)
          | exact resolve b2e193312 b2e485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e485 b2e193312
        have b2e195730 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (k X0 (M.op x y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e193363 x y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e193363
          | exact resolve b2e193363 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e193363
        have b2e195750 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e195730 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e195730
          | (have j0 := b2e195730 X0
             grind)
          | exact resolve b2e195730 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e195730
        have b2e226111 : ∀ X0 X1 : G, (k X1 (M.op X1 X0)) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15619 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e15619
          | exact resolve b2e15619 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15619
        have b2e247878 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e44884
        have b2e247882 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e247878
             have r₂ := b2e894
             grind)
          | exact resolve b2e247878 b2e894
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e894 b2e247878
        have b2e271443 : ∀ X0 : G, (M.op X0 (σ x)) = (σ (k x (τ X0))) ∨ (σ x) = (σ (k x (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e56105 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e56105
          | (have j0 := b2e56105 (τ X0)
             grind)
          | exact resolve b2e56105 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56105
        have b2e271630 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (σ (k x (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e271443 X0
             have i₂ := b2e27 X0 x
             grind)
          | exact superpose b2e27 b2e271443
          | (have j0 := b2e271443 X0
             grind)
          | exact resolve b2e271443 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e271443
        have b2e271646 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e271630 X0
             have i₂ := b2e27 X0 x
             grind)
          | exact superpose b2e27 b2e271630
          | (have j0 := b2e271630 X0
             grind)
          | exact resolve b2e271630 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e271630
        have b2e298425 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k (τ (σ (M.op X0 x))) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e73154 (σ (M.op X0 x))
             have i₂ := b2e90015 X0 (σ x)
             grind)
          | exact superpose b2e90015 b2e73154
          | (have j0 := b2e73154 (σ y)
             have j1 := b2e90015 X0 x
             grind)
          | exact resolve b2e73154 b2e90015
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90015
        have b2e298426 : (τ (M.op (σ x) (σ y))) = (k (τ (σ (M.op y x))) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b2e73154 (σ (M.op y x))
             have i₂ := b2e68732 (σ x)
             grind)
          | exact superpose b2e68732 b2e73154
          | (have j0 := b2e73154 (σ y)
             grind)
          | exact resolve b2e73154 b2e68732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68732 b2e73154
        have b2e298518 : (τ (M.op (σ x) (σ y))) = (k (τ (σ (M.op y x))) x) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b2e298426
             have r₂ := b2e21
             grind)
          | exact resolve b2e298426 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298426
        have b2e298519 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k (τ (σ (M.op X0 x))) x) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e298425 X0
             grind)
          | (have r₁ := b2e298425 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e298425 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298425
        have b2e298541 : (k (M.op y x) x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b2e298518
             have i₂ := b2e13 (M.op y x)
             grind)
          | exact superpose b2e13 b2e298518
          | exact resolve b2e298518 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298518
        have b2e298542 : ∀ X0 : G, (k (M.op X0 x) x) = (τ (M.op (σ x) (σ y))) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e298519 X0
             have i₂ := b2e13 (M.op X0 x)
             grind)
          | exact superpose b2e13 b2e298519
          | (have j0 := b2e298519 X0
             grind)
          | exact resolve b2e298519 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298519
        have b2e298554 : (k (M.op y x) x) = (τ (σ y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b2e298541
             have i₂ := b2e256
             grind)
          | exact superpose b2e256 b2e298541
          | exact resolve b2e298541 b2e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298541
        have b2e298555 : ∀ X0 : G, (k (M.op X0 x) x) = (τ (σ y)) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e298542 X0
             have i₂ := b2e256
             grind)
          | exact superpose b2e256 b2e298542
          | (have j0 := b2e298542 X0
             grind)
          | exact resolve b2e298542 b2e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298542
        have b2e298557 : y = (k (M.op y x) x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b2e298554
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e298554
          | exact resolve b2e298554 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298554
        have b2e298558 : ∀ X0 : G, y = (k (M.op X0 x) x) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e298555 X0
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e298555
          | (have j0 := b2e298555 X0
             grind)
          | exact resolve b2e298555 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298555
        have b2e298560 : y = (M.op y x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b2e298557
             have i₂ := b2e132
             grind)
          | exact superpose b2e132 b2e298557
          | exact resolve b2e298557 b2e132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e132 b2e298557
        have b2e298561 : y = (M.op y x) := by grind
        clear b2e298560
        have b2e298562 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e298558 X0
             have i₂ := b2e174 X0
             grind)
          | exact superpose b2e174 b2e298558
          | (have j0 := b2e298558 X0
             grind)
          | exact resolve b2e298558 b2e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e174 b2e298558
        have b2e300763 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e307 X0
             have i₂ := b2e298561
             grind)
          | exact superpose b2e298561 b2e307
          | exact resolve b2e307 b2e298561
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e307
        have b2e300778 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e107337
             have i₂ := b2e298561
             grind)
          | exact superpose b2e298561 b2e107337
          | exact resolve b2e107337 b2e298561
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e107337
        have b2e300883 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e300778
        have b2e306427 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e2056 y x
             have i₂ := b2e300883
             grind)
          | exact superpose b2e300883 b2e2056
          | (have j0 := b2e2056 y X0
             grind)
          | exact resolve b2e2056 b2e300883
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2056
        have b2e306454 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e2097 X0 (σ y) y
             have i₂ := b2e300883
             grind)
          | exact superpose b2e300883 b2e2097
          | (have j0 := b2e2097 X0 x y
             grind)
          | exact resolve b2e2097 b2e300883
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2097 b2e300883
        have b2e306553 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b2e306454 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e306454
        have b2e306558 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e306427 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e306427
        have b2e434720 : ∀ X0 : G, y ≠ (M.op y x) ∨ (M.op y (σ X0)) = (k (σ X0) y) ∨ y = (M.op y (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e15530 y X0
             have i₂ := b2e41 y
             grind)
          | exact superpose b2e41 b2e15530
          | (have j0 := b2e15530 y X0
             grind)
          | exact resolve b2e15530 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15530
        have b2e434731 : ∀ X0 : G, (M.op y (σ X0)) = (k (σ X0) y) ∨ y = (M.op y (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e434720 X0
             grind)
          | (have r₁ := b2e434720 X0
             have r₂ := b2e298561
             grind)
          | exact resolve b2e434720 b2e298561
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298561 b2e434720
        have b2e435808 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e434731 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e434731
          | exact resolve b2e434731 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e434731
        have b2e436017 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op X0 x) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e298562 X0
             have i₂ := b2e435808 X0
             grind)
          | exact superpose b2e435808 b2e298562
          | (have j0 := b2e298562 X0
             have j1 := b2e435808 X0
             grind)
          | exact resolve b2e298562 b2e435808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298562
        have b2e437209 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (k x X0) ∨ (M.op y X0) = X0 ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e226111 x X0
             have i₂ := b2e436017 X0
             grind)
          | exact superpose b2e436017 b2e226111
          | (have j1 := b2e436017 X0
             grind)
          | exact resolve b2e226111 b2e436017
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e226111 b2e436017
        have b2e437396 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (k x X0) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b2e437209 X0
             have j1 := b2e192770 X0 y
             grind)
          | (have r₁ := b2e437209 X0
             have r₂ := b2e192770 X0 y
             grind)
          | (have r₁ := b2e437209 y
             have r₂ := b2e192770 y y
             grind)
          | exact resolve b2e437209 b2e192770
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e192770 b2e437209
        have b2e437434 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e437396 X0
             have j1 := b2e300763 X0
             grind)
          | (have r₁ := b2e437396 X0
             have r₂ := b2e300763 X0
             grind)
          | exact resolve b2e437396 b2e300763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e300763 b2e437396
        have b2e437579 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) ∨ y = (k x (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e26 X0 y
             have i₂ := b2e437434 (τ X0)
             grind)
          | exact superpose b2e437434 b2e26
          | (have j1 := b2e437434 (τ X0)
             grind)
          | exact resolve b2e26 b2e437434
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e437434
        have b2e437767 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (k x (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e437579 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e437579
          | (have j0 := b2e437579 X0
             grind)
          | exact resolve b2e437579 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e437579
        have b2e438871 : ∀ X0 : G, (σ y) = (k (σ x) X0) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e27 X0 x
             have i₂ := b2e437767 X0
             grind)
          | exact superpose b2e437767 b2e27
          | (have j1 := b2e437767 X0
             grind)
          | exact resolve b2e27 b2e437767
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e437767
        have b2e439756 : ∀ X0 : G, (σ y) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e271646 X0
             have i₂ := b2e438871 X0
             grind)
          | exact superpose b2e438871 b2e271646
          | (have j1 := b2e438871 X0
             grind)
          | exact resolve b2e271646 b2e438871
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e271646
        have b2e439908 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ y))) ∨ (σ y) = (k (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e125 X0 (σ y)
             have i₂ := b2e438871 (σ X0)
             grind)
          | exact superpose b2e438871 b2e125
          | (have j1 := b2e438871 (σ X0)
             grind)
          | exact resolve b2e125 b2e438871
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e438871
        have b2e439934 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) ∨ (σ y) = (k (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e439908 X0
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e439908
          | (have j0 := b2e439908 X0
             grind)
          | exact resolve b2e439908 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e439908
        have b2e439985 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ y) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b2e439756 X0
             grind)
          | (have r₁ := b2e439756 X0
             have r₂ := b2e259
             grind)
          | exact resolve b2e439756 b2e259
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e439756
        have b2e440005 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ y) = (k (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e439934 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e439934
          | (have j0 := b2e439934 X0
             grind)
          | exact resolve b2e439934 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e439934
        have b2e440042 : ∀ X0 : G, (σ y) = (σ (k x X0)) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e440005 X0
             have i₂ := b2e18 x X0
             grind)
          | exact superpose b2e18 b2e440005
          | (have j0 := b2e440005 X0
             grind)
          | exact resolve b2e440005 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e440005
        have b2e440266 : ∀ X0 : G, (σ x) = (σ y) ∨ (τ (M.op X0 (σ x))) = (k (τ (M.op X0 (σ x))) y) := by
          intro X0
          first
          | (have i₁ := b2e440042 (τ (M.op X0 (σ x)))
             have i₂ := b2e1128 X0
             grind)
          | exact superpose b2e1128 b2e440042
          | (have j0 := b2e440042 (τ (M.op X0 (σ x)))
             grind)
          | exact resolve b2e440042 b2e1128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1128 b2e440042
        have b2e440563 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ (M.op X0 (σ x))) y) := by
          intro X0
          first
          | (have j0 := b2e440266 X0
             grind)
          | (have r₁ := b2e440266 X0
             have r₂ := b2e259
             grind)
          | exact resolve b2e440266 b2e259
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e440266
        have b2e441383 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ y))) ∨ (σ y) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e125 X0 (σ y)
             have i₂ := b2e439985 (σ X0)
             grind)
          | exact superpose b2e439985 b2e125
          | (have j1 := b2e439985 (σ X0)
             grind)
          | exact resolve b2e125 b2e439985
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e125 b2e439985
        have b2e441481 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) ∨ (σ y) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e441383 X0
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e441383
          | (have j0 := b2e441383 X0
             grind)
          | exact resolve b2e441383 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e441383
        have b2e441491 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ x)) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e441481 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e441481
          | (have j0 := b2e441481 X0
             grind)
          | exact resolve b2e441481 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e441481
        have b2e442091 : ∀ X0 : G, (σ y) ≠ (σ (τ (M.op X0 (σ x)))) ∨ (σ y) = (M.op (σ y) (σ (τ (M.op X0 (σ x))))) := by
          intro X0
          first
          | (have i₁ := b2e306558 (τ (M.op X0 (σ x)))
             have i₂ := b2e440563 X0
             grind)
          | exact superpose b2e440563 b2e306558
          | (have j0 := b2e306558 (τ (M.op X0 (σ x)))
             grind)
          | exact resolve b2e306558 b2e440563
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e306558 b2e440563
        have b2e442106 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ (τ (M.op X0 (σ x))))) := by
          intro X0
          first
          | (have i₁ := b2e442091 X0
             have i₂ := b2e14 (M.op X0 (σ x))
             grind)
          | exact superpose b2e14 b2e442091
          | (have j0 := b2e442091 X0
             grind)
          | exact resolve b2e442091 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e442091
        have b2e442135 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) ∨ (σ y) ≠ (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e442106 X0
             have i₂ := b2e14 (M.op X0 (σ x))
             grind)
          | exact superpose b2e14 b2e442106
          | (have j0 := b2e442106 X0
             grind)
          | exact resolve b2e442106 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e442106
        have b2e442152 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) ≠ (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e442135 X0
             have i₂ := b2e36 (σ x) (σ y) X0
             grind)
          | exact superpose b2e36 b2e442135
          | (have j0 := b2e442135 X0
             grind)
          | exact resolve b2e442135 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e442135
        have b2e442154 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b2e442152 X0
             grind)
          | (have r₁ := b2e442152 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e442152 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e442152
        have b2e443400 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e442154 (σ X0)
             have i₂ := b2e441491 X0
             grind)
          | exact superpose b2e441491 b2e442154
          | (have j1 := b2e441491 X0
             grind)
          | (have r₁ := b2e442154 (σ X0)
             have r₂ := b2e441491 X0
             grind)
          | exact resolve b2e442154 b2e441491
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e441491
        have b2e443496 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e443400 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e443400
        have b2e443595 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e435808 X0
             have i₂ := b2e443496 X0
             grind)
          | exact superpose b2e443496 b2e435808
          | (have j0 := b2e435808 X0
             grind)
          | exact resolve b2e435808 b2e443496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e435808
        have b2e443720 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e26 X0 y
             have i₂ := b2e443496 (τ X0)
             grind)
          | exact superpose b2e443496 b2e26
          | exact resolve b2e26 b2e443496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e443496
        have b2e443852 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e443720 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e443720
          | exact resolve b2e443720 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e443720
        have b2e446816 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y X0) ∨ y = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e443595 (M.op x X1)
             have i₂ := b2e36 X1 y x
             grind)
          | exact superpose b2e36 b2e443595
          | (have j0 := b2e443595 X0
             grind)
          | exact resolve b2e443595 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e450292 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = y ∨ y = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e443595 X0
             have i₂ := b2e446816 X0 y
             grind)
          | (have i₁ := b2e443595 X0
             have i₂ := b2e446816 X0 X1
             grind)
          | exact superpose b2e446816 b2e443595
          | (have j0 := b2e443595 X1
             have j1 := b2e446816 X1 X1
             grind)
          | exact resolve b2e443595 b2e446816
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e443595
        have b2e450574 : ∀ X0 X1 : G, (M.op X1 X0) ≠ y ∨ y = (M.op y X0) := by
          intro X0 X1
          first
          | (have j0 := b2e446816 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e446816
        have b2e450656 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ y = (M.op y X1) := by
          intro X0 X1
          first
          | (have j0 := b2e450292 X0 X1
             have j1 := b2e450574 X1 X1
             grind)
          | (have r₁ := b2e450292 X1 y
             have r₂ := b2e450574 y X1
             grind)
          | (have r₁ := b2e450292 X1 X0
             have r₂ := b2e450574 X0 X1
             grind)
          | (have r₁ := b2e450292 X0 X0
             have r₂ := b2e450574 X0 y
             grind)
          | exact resolve b2e450292 b2e450574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e450292 b2e450574
        have b2e451812 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 y) ∨ (M.op X2 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e36 X1 X0 y
             have i₂ := b2e450656 X2 X1
             grind)
          | exact superpose b2e450656 b2e36
          | (have j1 := b2e450656 X2 X1
             grind)
          | exact resolve b2e36 b2e450656
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e450656
        have b2e452116 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 x) ∨ (M.op X2 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e451812 X0 X1 X2
             have i₂ := b2e41 X0
             grind)
          | exact superpose b2e41 b2e451812
          | (have j0 := b2e451812 X0 X1 X2
             grind)
          | exact resolve b2e451812 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e451812
        have b2e476224 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e64
             have i₂ := b2e452116 x X0 X1
             grind)
          | (have i₁ := b2e64
             have i₂ := b2e452116 x x x
             grind)
          | exact superpose b2e452116 b2e64
          | (have j1 := b2e452116 X0 X0 X1
             grind)
          | exact resolve b2e64 b2e452116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64 b2e452116
        have b2e477639 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 x) = X0 ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e195750 X0
             have i₂ := b2e476224 X0 x
             grind)
          | exact superpose b2e476224 b2e195750
          | (have j0 := b2e195750 X0
             have j1 := b2e476224 X0 x
             grind)
          | (have r₁ := b2e195750 x
             have r₂ := b2e476224 x x
             grind)
          | (have r₁ := b2e195750 X0
             have r₂ := b2e476224 X0 x
             grind)
          | exact resolve b2e195750 b2e476224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e195750 b2e476224
        have b2e477706 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b2e477639 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e477639
        have b2e477776 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b2e477706 X0
             have j1 := b2e600 X0
             grind)
          | (have r₁ := b2e477706 X0
             have r₂ := b2e600 X0
             grind)
          | exact resolve b2e477706 b2e600
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e600 b2e477706
        have b2e478096 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e26 X0 x
             have i₂ := b2e477776 (τ X0)
             grind)
          | exact superpose b2e477776 b2e26
          | exact resolve b2e26 b2e477776
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e477776
        have b2e478217 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e478096 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e478096
          | exact resolve b2e478096 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478096
        have b2e478301 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e19895 X0
             have i₂ := b2e478217 X0
             grind)
          | exact superpose b2e478217 b2e19895
          | (have j0 := b2e19895 X0
             grind)
          | exact resolve b2e19895 b2e478217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19895 b2e478217
        have b2e587618 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (σ x)) ∨ (M.op (σ x) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e36 X1 X0 (σ x)
             have i₂ := b2e478301 X1
             grind)
          | exact superpose b2e478301 b2e36
          | (have j1 := b2e478301 X1
             grind)
          | exact resolve b2e36 b2e478301
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e587771 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ x) X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e478301 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478301
        have b2e884997 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (σ y) ∨ (M.op (σ x) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e442154 X0
             have i₂ := b2e587618 X0 X1
             grind)
          | (have i₁ := b2e442154 X0
             have i₂ := b2e587618 X0 (σ x)
             grind)
          | exact superpose b2e587618 b2e442154
          | (have j1 := b2e587618 X0 X1
             grind)
          | exact resolve b2e442154 b2e587618
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e442154
        have b2e885041 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ (M.op (σ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e247882
             have i₂ := b2e587618 (σ y) X0
             grind)
          | (have i₁ := b2e247882
             have i₂ := b2e587618 (σ y) (σ x)
             grind)
          | exact superpose b2e587618 b2e247882
          | (have j1 := b2e587618 X0 X0
             grind)
          | exact resolve b2e247882 b2e587618
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e247882 b2e587618
        have b2e885258 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (σ y) ∨ (M.op X2 X1) = (M.op (σ x) (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e884997 (M.op X0 X0) (M.op X2 X1)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e884997
          | (have j0 := b2e884997 X0 X1
             grind)
          | exact resolve b2e884997 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e885385 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (σ y) ∨ (M.op X2 X1) = (M.op (σ x) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e885258 X0 X1 X2
             have i₂ := b2e36 X1 (σ x) X2
             grind)
          | exact superpose b2e36 b2e885258
          | (have j0 := b2e885258 X0 X1 X2
             grind)
          | exact resolve b2e885258 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e885258
        have b2e988672 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e885385 (σ x) (σ y) x
             have i₂ := b2e256
             grind)
          | exact superpose b2e256 b2e885385
          | (have r₁ := b2e885385 (σ x) (σ y) x
             have r₂ := b2e256
             grind)
          | exact resolve b2e885385 b2e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e256 b2e885385
        have b2e988691 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e988672 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e988672
        have b2e1478936 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e443852 X0
             have i₂ := b2e306553 X0
             grind)
          | exact superpose b2e306553 b2e443852
          | (have j1 := b2e306553 X0
             grind)
          | exact resolve b2e443852 b2e306553
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e306553 b2e443852
        have b2e1479086 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (σ y)) ∨ (M.op (σ y) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e36 X1 X0 (σ y)
             have i₂ := b2e1478936 X1
             grind)
          | exact superpose b2e1478936 b2e36
          | (have j1 := b2e1478936 X1
             grind)
          | exact resolve b2e36 b2e1478936
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e1478936
        have b2e1479205 : ∀ X0 X1 : G, (M.op X0 X1) = (σ y) ∨ (M.op (σ y) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e1479086 X0 X1
             have i₂ := b2e988691 X0
             grind)
          | exact superpose b2e988691 b2e1479086
          | (have j0 := b2e1479086 X0 X1
             grind)
          | exact resolve b2e1479086 b2e988691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e988691 b2e1479086
        have b2e1482306 : ∀ X0 X1 : G, (σ x) = X0 ∨ (M.op (σ x) X0) = X0 ∨ (M.op X1 X0) = (σ y) := by
          intro X0 X1
          first
          | (have i₁ := b2e885041 X0
             have i₂ := b2e1479205 X1 X0
             grind)
          | exact superpose b2e1479205 b2e885041
          | (have j0 := b2e885041 X0
             have j1 := b2e1479205 X1 X0
             grind)
          | exact resolve b2e885041 b2e1479205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e885041 b2e1479205
        have b2e1482688 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ (M.op X1 X0) = (σ y) := by
          intro X0 X1
          first
          | (have j0 := b2e1482306 X0 X1
             have j1 := b2e587771 X0
             grind)
          | (have r₁ := b2e1482306 X0 X1
             have r₂ := b2e587771 X0
             grind)
          | (have r₁ := b2e1482306 (σ x) X1
             have r₂ := b2e587771 (σ x)
             grind)
          | (have r₁ := b2e1482306 (σ x) X1
             have r₂ := b2e587771 (M.op (σ x) (σ x))
             grind)
          | exact resolve b2e1482306 b2e587771
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e587771 b2e1482306
        have b2e1482949 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e1482688 X0 x
             have j1 := b2e884997 X0 X0
             grind)
          | (have r₁ := b2e1482688 (σ y) x
             have r₂ := b2e884997 (σ x) (σ y)
             grind)
          | (have r₁ := b2e1482688 x X0
             have r₂ := b2e884997 X0 x
             grind)
          | exact resolve b2e1482688 b2e884997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e884997 b2e1482688
        have b2e1485230 : y = (M.op (σ x) x) := by
          first
          | (have i₁ := b2e41 (σ x)
             have i₂ := b2e1482949 y
             grind)
          | exact superpose b2e1482949 b2e41
          | exact resolve b2e41 b2e1482949
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e1485252 : x = y := by
          first
          | (have i₁ := b2e1485230
             have i₂ := b2e1482949 x
             grind)
          | exact superpose b2e1482949 b2e1485230
          | exact resolve b2e1485230 b2e1482949
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1482949 b2e1485230
        have b2e1485854 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e259
             have i₂ := b2e1485252
             grind)
          | exact superpose b2e1485252 b2e259
          | exact resolve b2e259 b2e1485252
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e259 b2e1485252
        have b2e1487813 : False := by grind
        exact b2e1487813
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 X0) y) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 (M.op X3 X1) (M.op X0 X0)
             have i₂ := b3e12 X0 X1 X3
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
          intro X1 X2 X3
          first
          | (have i₁ := b3e34 x X1 X2 X3
             have i₂ := b3e12 X2 X1 x
             grind)
          | exact superpose b3e12 b3e34
          | exact resolve b3e34 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e61 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X1 X1) (M.op X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 y (M.op X0 X0)
             have i₂ := b3e32 X0
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e63 : ∀ X1 : G, (M.op X1 y) = (M.op X1 x) := by
          intro X1
          first
          | (have i₁ := b3e61 x X1
             have i₂ := b3e12 X1 x x
             grind)
          | exact superpose b3e12 b3e61
          | exact resolve b3e61 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e69 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e36 (σ y) X0 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e36
          | exact resolve b3e36 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e93 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e63 x
             grind)
          | exact superpose b3e63 b3e23
          | exact resolve b3e23 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e94 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e63 x
             grind)
          | exact superpose b3e63 b3e20
          | exact resolve b3e20 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e149 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e69 (σ x)
             grind)
          | exact superpose b3e69 b3e22
          | exact resolve b3e22 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e69
        have b3e178 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e149
             grind)
          | exact superpose b3e149 b3e15
          | (have j0 := b3e15 (σ x) (σ x)
             grind)
          | (have r₁ := b3e15 (σ x) (σ x)
             have r₂ := b3e149
             grind)
          | exact resolve b3e15 b3e149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e149
        have b3e179 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b3e178
        have b3e180 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e179
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e179
          | exact resolve b3e179 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e179
        have b3e211 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e180
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e180
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e180 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e180
        have b3e215 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b3e211
        have b3e219 : x = (M.op x x) := by
          first
          | (have r₁ := b3e215
             have r₂ := b3e93
             grind)
          | exact resolve b3e215 b3e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e93 b3e215
        have b3e220 : False := by grind
        exact b3e220
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op x y) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e37 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 X0) y) := by
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
          have b4e39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op X3 X1) (M.op X0 X0)
               have i₂ := b4e13 X0 X1 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e39 x X1 X2 X3
               have i₂ := b4e13 X2 X1 x
               grind)
            | exact superpose b4e13 b4e39
            | exact resolve b4e39 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e44 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X1 X1) (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 y (M.op X0 X0)
               have i₂ := b4e37 X0
               grind)
            | exact superpose b4e37 b4e13
            | exact resolve b4e13 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e46 : ∀ X1 : G, (M.op X1 y) = (M.op X1 x) := by
            intro X1
            first
            | (have i₁ := b4e44 x X1
               have i₂ := b4e13 X1 x x
               grind)
            | exact superpose b4e13 b4e44
            | exact resolve b4e44 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e46 x
               grind)
            | exact superpose b4e46 b4e21
            | exact resolve b4e21 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e83 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e41 (σ x) X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e41
            | exact resolve b4e41 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e133 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e83 (σ x)
               grind)
            | exact superpose b4e83 b4e20
            | exact resolve b4e20 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e134 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e83 (σ x)
               grind)
            | exact superpose b4e83 b4e23
            | exact resolve b4e23 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83
          have b4e135 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e133
               have i₂ := b4e46 x
               grind)
            | exact superpose b4e46 b4e133
            | exact resolve b4e133 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46 b4e133
          have b4e550 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e135
               have i₂ := b4e62 x x
               grind)
            | exact superpose b4e62 b4e135
            | (have j1 := b4e62 x x
               grind)
            | exact resolve b4e135 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62 b4e135
          have b4e551 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e550
          have b4e552 : (σ (M.op x x)) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b4e551
               have r₂ := b4e134
               grind)
            | exact resolve b4e551 b4e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134 b4e551
          have b4e575 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e552
               have i₂ := b4e18 x x
               grind)
            | exact superpose b4e18 b4e552
            | (have j1 := b4e18 x x
               grind)
            | exact resolve b4e552 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e552
          have b4e576 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b4e575
          have b4e577 : x = (M.op x x) := by grind
          clear b4e576
          have b4e578 : False := by grind
          exact b4e578
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : y ≠ y ∨ y = (k y x) := by
            first
            | (have i₁ := b5e16 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y x
               grind)
            | (have r₁ := b5e16 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e26 : y = (k y x) := by grind
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
          have b5e33 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 X1)) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X0 X0) X1 X2
               have i₂ := b5e13 X0 X0 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 X0) y) := by
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
          have b5e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X3 X1) (M.op X0 X0)
               have i₂ := b5e13 X0 X1 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 (M.op X0 X0) (M.op X2 X1)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e16
            | (have j0 := b5e16 (M.op X0 X0) (M.op X2 X1)
               grind)
            | (have r₁ := b5e16 (M.op X1 X1) (M.op X2 X1)
               have r₂ := b5e13 X1 X1 X2
               grind)
            | exact resolve b5e16 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
            intro X1 X2 X3
            first
            | (have i₁ := b5e35 x X1 X2 X3
               have i₂ := b5e13 X2 X1 x
               grind)
            | exact superpose b5e13 b5e35
            | exact resolve b5e35 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e38 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X0 X1 x
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e33
            | exact resolve b5e33 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e40 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X1 X1) (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 y (M.op X0 X0)
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X1 : G, (M.op X1 y) = (M.op X1 x) := by
            intro X1
            first
            | (have i₁ := b5e40 x X1
               have i₂ := b5e13 X1 x x
               grind)
            | exact superpose b5e13 b5e40
            | exact resolve b5e40 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e44 : y ≠ y ∨ x = (M.op x y) ∨ x = (k x y) := by
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
          have b5e45 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X0 X0)) ∨ (M.op X2 X1) = (k (M.op X2 X1) (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 (M.op X2 X1) (M.op X0 X0)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 (M.op X2 X1) (M.op X0 X0)
               grind)
            | (have r₁ := b5e17 (M.op X2 X1) (M.op X1 X1)
               have r₂ := b5e13 X1 X1 X2
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e47 : x = (M.op x y) ∨ x = (k x y) := by grind
          clear b5e44
          have b5e49 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X2 X1) = (k (M.op X2 X1) (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e45 X0 X1 X2
               have j1 := b5e16 (M.op X2 X1) (M.op X0 X0)
               grind)
            | (have r₁ := b5e45 X0 X1 X2
               have r₂ := b5e16 (M.op X2 X1) (M.op X0 X0)
               grind)
            | exact resolve b5e45 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e50 : x = (k x y) := by
            first
            | (have j1 := b5e16 x y
               grind)
            | (have r₁ := b5e47
               have r₂ := b5e16 x y
               grind)
            | exact resolve b5e47 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e55 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e27 X1 X0
               have i₂ := b5e18 (τ X1) X0
               grind)
            | exact superpose b5e18 b5e27
            | (have j1 := b5e18 (τ X1) X0
               grind)
            | exact resolve b5e27 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e65 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e42 x
               grind)
            | exact superpose b5e42 b5e21
            | exact resolve b5e21 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X0 X1) X2 X3
               have i₂ := b5e37 X1 (M.op X0 X1) X0
               grind)
            | exact superpose b5e37 b5e13
            | exact resolve b5e13 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e81 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X2 X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X0 (M.op X2 X1)
               have i₂ := b5e37 X1 X0 X2
               grind)
            | exact superpose b5e37 b5e16
            | (have j0 := b5e16 X0 X1
               grind)
            | exact resolve b5e16 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e85 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e78 X0 X1 X2 x
               have i₂ := b5e37 X2 (M.op (M.op X0 X1) X1) x
               grind)
            | exact superpose b5e37 b5e78
            | exact resolve b5e78 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e103 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X1 (M.op X0 X0)
               have i₂ := b5e38 X0 X1
               grind)
            | exact superpose b5e38 b5e17
            | (have j0 := b5e17 X1 (M.op X0 X0)
               grind)
            | (have r₁ := b5e17 X1 (M.op X1 X1)
               have r₂ := b5e38 X1 X1
               grind)
            | exact resolve b5e17 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e110 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e103 X0 X1
               have j1 := b5e16 X1 (M.op X0 X0)
               grind)
            | (have r₁ := b5e103 X0 X0
               have r₂ := b5e16 X0 (M.op X0 X0)
               grind)
            | exact resolve b5e103 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103
          have b5e116 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 (τ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e28 X0 X1
               have i₂ := b5e18 X1 (τ X0)
               grind)
            | exact superpose b5e18 b5e28
            | (have j1 := b5e18 X1 (τ X0)
               grind)
            | exact resolve b5e28 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e121 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e132 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e36 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e145 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e32
            | exact resolve b5e32 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e162 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e49 X1 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e213 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e54 x y
               grind)
            | exact superpose b5e54 b5e24
            | (have j1 := b5e54 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e54 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e54 y x
               grind)
            | exact resolve b5e24 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e216 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (M.op X1 (σ X0)) = (M.op X1 (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e37 (σ X2) X1 (σ X0)
               have i₂ := b5e54 X2 X0
               grind)
            | exact superpose b5e54 b5e37
            | (have j1 := b5e54 X2 X0
               grind)
            | exact resolve b5e37 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e217 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X1) (σ X0)
               have i₂ := b5e54 X1 X0
               grind)
            | exact superpose b5e54 b5e17
            | (have j0 := b5e17 (σ X1) (σ X0)
               have j1 := b5e54 X1 X0
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e54 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X0)
               have r₂ := b5e54 X0 X1
               grind)
            | exact resolve b5e17 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e220 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e54 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e222 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e220 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e220
          have b5e224 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e217 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e217
          have b5e225 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e224 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e224
          have b5e226 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e213
          have b5e236 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e225 X0 X1
               have j1 := b5e16 (σ X1) (σ X0)
               grind)
            | (have r₁ := b5e225 X0 X1
               have r₂ := b5e16 (σ X1) (σ X0)
               grind)
            | exact resolve b5e225 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e225
          have b5e237 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b5e226
               have r₂ := b5e23
               grind)
            | exact resolve b5e226 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e226
          have b5e246 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e236 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e236
            | (have j0 := b5e236 X0 X1
               grind)
            | exact resolve b5e236 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e236
          have b5e247 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e237
               have i₂ := b5e26
               grind)
            | exact superpose b5e26 b5e237
            | exact resolve b5e237 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e237
          have b5e250 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e247
               grind)
            | exact superpose b5e247 b5e20
            | exact resolve b5e20 b5e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e247
          have b5e259 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e250
               have i₂ := b5e42 x
               grind)
            | exact superpose b5e42 b5e250
            | exact resolve b5e250 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e250
          have b5e264 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e132 (σ X1) X1
               have i₂ := b5e54 X1 X1
               grind)
            | exact superpose b5e54 b5e132
            | (have j1 := b5e54 X0 X0
               grind)
            | exact resolve b5e132 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e268 : ∀ X0 : G, (M.op y y) = (k (M.op y y) (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e132 y (M.op X0 X0)
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e132
            | exact resolve b5e132 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e132
          have b5e276 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e264 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e264
          have b5e277 : ∀ X0 : G, (M.op y x) = (k (M.op y x) (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e268 X0
               have i₂ := b5e42 y
               grind)
            | exact superpose b5e42 b5e268
            | exact resolve b5e268 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e268
          have b5e285 : ∀ X0 : G, y = (k y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e277 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e277
            | exact resolve b5e277 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e277
          have b5e298 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b5e162 X0 y
               have i₂ := b5e42 y
               grind)
            | exact superpose b5e42 b5e162
            | exact resolve b5e162 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e309 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) y) := by
            intro X0
            first
            | (have i₁ := b5e298 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e298
            | exact resolve b5e298 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e298
          have b5e315 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) y) := by
            intro X0
            first
            | (have i₁ := b5e309 x
               have i₂ := b5e42 x
               grind)
            | exact superpose b5e42 b5e309
            | exact resolve b5e309 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e309
          have b5e335 : y = (k y y) := by
            first
            | (have i₁ := b5e285 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e285
            | exact resolve b5e285 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e285
          have b5e369 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X2 (M.op (M.op X0 X1) X1)) = X2 ∨ (k X2 (M.op (M.op X0 X1) X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X2 (M.op (M.op X0 X1) X1)
               have i₂ := b5e85 X0 X1 X2
               grind)
            | exact superpose b5e85 b5e17
            | (have j0 := b5e17 X2 (M.op (M.op X0 X1) X1)
               grind)
            | (have r₁ := b5e17 X2 (M.op (M.op X0 X2) X2)
               have r₂ := b5e85 X0 X2 X2
               grind)
            | exact resolve b5e17 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e383 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X2) ∨ (k X2 (M.op (M.op X0 X1) X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e369 X0 X1 X2
               have j1 := b5e16 X2 (M.op (M.op X0 X1) X1)
               grind)
            | (have r₁ := b5e369 X0 X1 X0
               have r₂ := b5e16 X0 (M.op (M.op X0 X1) X1)
               grind)
            | exact resolve b5e369 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e369
          have b5e477 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b5e110 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e110
          have b5e703 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e222 (M.op X0 X0)
               have i₂ := b5e162 X0 X0
               grind)
            | exact superpose b5e162 b5e222
            | (have j0 := b5e222 (M.op X0 X0)
               grind)
            | exact resolve b5e222 b5e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e162
          have b5e706 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e222 y
               have i₂ := b5e335
               grind)
            | exact superpose b5e335 b5e222
            | (have j0 := b5e222 y
               grind)
            | exact resolve b5e222 b5e335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e335
          have b5e708 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e222 (τ X0)
               have i₂ := b5e28 X0 (τ X0)
               grind)
            | exact superpose b5e28 b5e222
            | (have j0 := b5e222 (τ X0)
               grind)
            | exact resolve b5e222 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e709 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e706
          have b5e710 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b5e703 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e703
          have b5e713 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e708 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e708
            | (have j0 := b5e708 X0
               grind)
            | exact resolve b5e708 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e708
          have b5e716 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e713 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e713
            | (have j0 := b5e713 X0
               grind)
            | exact resolve b5e713 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e713
          have b5e773 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e716 (τ X0)
               have i₂ := b5e145 X0 X0
               grind)
            | exact superpose b5e145 b5e716
            | (have j0 := b5e716 (τ X0)
               grind)
            | exact resolve b5e716 b5e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e839 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e246 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e246
            | exact resolve b5e246 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e246
          have b5e891 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e839 X0 X1
               have i₂ := b5e28 X0 X1
               grind)
            | exact superpose b5e28 b5e839
            | (have j0 := b5e839 X0 X1
               grind)
            | exact resolve b5e839 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e839
          have b5e894 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e891 X0 X1
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e891
            | (have j0 := b5e891 X0 X1
               grind)
            | exact resolve b5e891 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e891
          have b5e1011 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e55 X0 (σ X0)
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e55
            | exact resolve b5e55 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e1049 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e1011 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e1011
            | (have j0 := b5e1011 X0 X1
               grind)
            | exact resolve b5e1011 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1011
          have b5e1678 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (σ X2)) ∨ (σ (k (τ X0) X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (M.op (σ X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e216 (τ X0) X1 X2
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e216
            | exact resolve b5e216 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1839 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ X0)) ∨ (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e709
               have i₂ := b5e216 X0 (σ y) y
               grind)
            | (have i₁ := b5e709
               have i₂ := b5e216 y (σ y) x
               grind)
            | exact superpose b5e216 b5e709
            | (have j1 := b5e216 X0 x y
               grind)
            | exact resolve b5e709 b5e216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1847 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e216 X1 (σ X0) X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1851 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e1839 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1839
          have b5e1887 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (M.op X1 X0) = (M.op X1 (σ X2)) ∨ (σ X2) = (M.op (σ X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1678 X0 X1 X2
               have i₂ := b5e27 X0 X2
               grind)
            | exact superpose b5e27 b5e1678
            | (have j0 := b5e1678 X0 X1 X2
               grind)
            | exact resolve b5e1678 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1678
          have b5e2599 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X1)) ∨ (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (k X1 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e216 X1 (σ (M.op X0 X0)) (M.op X0 X0)
               have i₂ := b5e710 X0
               grind)
            | exact superpose b5e710 b5e216
            | (have j0 := b5e216 X1 X1 (M.op X0 X0)
               grind)
            | exact resolve b5e216 b5e710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e216
          have b5e2635 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (k X1 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e2599 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2599
          have b5e4103 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e894 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e894
            | exact resolve b5e894 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4132 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e121 X0 (σ X1)
               have i₂ := b5e894 (σ X0) X1
               grind)
            | exact superpose b5e894 b5e121
            | (have j1 := b5e894 (σ X0) X1
               grind)
            | exact resolve b5e121 b5e894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e121 b5e894
          have b5e4217 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e4132 X0 X1
               have i₂ := b5e14 X1
               grind)
            | exact superpose b5e14 b5e4132
            | (have j0 := b5e4132 X0 X1
               grind)
            | exact resolve b5e4132 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4132
          have b5e4247 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e4217 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e4217
            | (have j0 := b5e4217 X0 X1
               grind)
            | exact resolve b5e4217 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4217
          have b5e4258 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e4247 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e4247
            | (have j0 := b5e4247 X0 X1
               grind)
            | exact resolve b5e4247 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4247
          have b5e4384 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e27 X0 X1
               have i₂ := b5e4103 X1 (τ X0)
               grind)
            | exact superpose b5e4103 b5e27
            | (have j1 := b5e4103 X1 (τ X0)
               grind)
            | exact resolve b5e27 b5e4103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e4103
          have b5e4403 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e4384 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e4384
            | (have j0 := b5e4384 X0 X1
               grind)
            | exact resolve b5e4384 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4384
          have b5e5346 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (σ (M.op X0 X1)) (σ X2)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e19 (k X1 X0) X2
               have i₂ := b5e1049 X1 X0
               grind)
            | exact superpose b5e1049 b5e19
            | (have j1 := b5e1049 X1 X0
               grind)
            | exact resolve b5e19 b5e1049
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1049
          have b5e5409 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (σ (k (M.op X0 X1) X2)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e5346 X0 X1 X2
               have i₂ := b5e19 (M.op X0 X1) X2
               grind)
            | exact superpose b5e19 b5e5346
            | (have j0 := b5e5346 X0 X1 X2
               grind)
            | exact resolve b5e5346 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5346
          have b5e5706 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) X0)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e383 X1 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e383
          have b5e11473 : ∀ X0 X1 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) (M.op X1 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e276 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e276
            | exact resolve b5e276 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e276
          have b5e11559 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) (M.op X1 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e11473 X0 X1
               have i₂ := b5e28 X0 (τ X0)
               grind)
            | exact superpose b5e28 b5e11473
            | (have j0 := b5e11473 X0 X1
               grind)
            | exact resolve b5e11473 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11473
          have b5e11589 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) (M.op X1 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e11559 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e11559
            | (have j0 := b5e11559 X0 X1
               grind)
            | exact resolve b5e11559 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11559
          have b5e11745 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (k X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e37 (σ X0) X2 (σ X1)
               have i₂ := b5e4258 X1 X0
               grind)
            | exact superpose b5e4258 b5e37
            | (have j1 := b5e4258 X1 X0
               grind)
            | exact resolve b5e37 b5e4258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4258
          have b5e15934 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b5e716 (σ X0)
               have i₂ := b5e4403 (σ X0) X0
               grind)
            | exact superpose b5e4403 b5e716
            | (have j0 := b5e716 (σ X0)
               have j1 := b5e4403 (σ X0) X0
               grind)
            | (have r₁ := b5e716 (σ x)
               have r₂ := b5e4403 (σ x) x
               grind)
            | exact resolve b5e716 b5e4403
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e716
          have b5e15935 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b5e773 (σ X0)
               have i₂ := b5e4403 (σ X0) X0
               grind)
            | exact superpose b5e4403 b5e773
            | (have j0 := b5e773 (σ X0)
               have j1 := b5e4403 (σ X0) X0
               grind)
            | exact resolve b5e773 b5e4403
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e773
          have b5e15991 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e28 X0 X1
               have i₂ := b5e4403 X0 X1
               grind)
            | exact superpose b5e4403 b5e28
            | (have j1 := b5e4403 X0 X1
               grind)
            | exact resolve b5e28 b5e4403
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e4403
          have b5e16088 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
            intro X0
            first
            | (have j0 := b5e15935 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15935
          have b5e16089 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
            intro X0
            first
            | (have j0 := b5e15934 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15934
          have b5e16184 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b5e16088 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e16088
            | (have j0 := b5e16088 X0
               grind)
            | exact resolve b5e16088 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16088
          have b5e16185 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e16089 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e16089
            | (have j0 := b5e16089 X0
               grind)
            | exact resolve b5e16089 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16089
          have b5e16275 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e16184 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e16184
            | (have j0 := b5e16184 X0
               grind)
            | exact resolve b5e16184 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16184
          have b5e20152 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e709
               have i₂ := b5e1887 X0 (σ y) y
               grind)
            | (have i₁ := b5e709
               have i₂ := b5e1887 (σ y) (σ y) x
               grind)
            | exact superpose b5e1887 b5e709
            | (have j1 := b5e1887 X0 x y
               grind)
            | exact resolve b5e709 b5e1887
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e709 b5e1887
          have b5e20169 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b5e20152 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20152
          have b5e24744 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e16185 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e16185
            | (have j0 := b5e16185 (τ X0)
               grind)
            | exact resolve b5e16185 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16185
          have b5e24943 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e24744 X0
               have i₂ := b5e145 X0 X0
               grind)
            | exact superpose b5e145 b5e24744
            | (have j0 := b5e24744 X0
               grind)
            | exact resolve b5e24744 b5e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e145 b5e24744
          have b5e29012 : ∀ X0 : G, (σ (τ (k X0 X0))) = (M.op (σ (τ (k X0 X0))) (σ (τ (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e710 (τ X0)
               have i₂ := b5e24943 X0
               grind)
            | exact superpose b5e24943 b5e710
            | (have j1 := b5e24943 (σ (τ (k X0 X0)))
               grind)
            | exact resolve b5e710 b5e24943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24943
          have b5e29066 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e29012 X0
               have i₂ := b5e15 (k X0 X0)
               grind)
            | exact superpose b5e15 b5e29012
            | (have j0 := b5e29012 (k X0 X0)
               grind)
            | exact resolve b5e29012 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29012
          have b5e39899 : (k x x) = (k (k x x) y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e11589 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e11589
            | (have j0 := b5e11589 x x
               grind)
            | exact resolve b5e11589 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11589
          have b5e39950 : (k x x) = (k (k x x) y) := by
            first
            | (have r₁ := b5e39899
               have r₂ := b5e65
               grind)
            | exact resolve b5e39899 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39899
          have b5e45975 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1847 (M.op X0 X0) X1
               have i₂ := b5e710 X0
               grind)
            | exact superpose b5e710 b5e1847
            | (have j0 := b5e1847 (M.op X0 X0) X1
               grind)
            | exact resolve b5e1847 b5e710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e710 b5e1847
          have b5e45998 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e45975 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45975
          have b5e47761 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e11745 X0 X0 x
               have i₂ := b5e16275 X0
               grind)
            | exact superpose b5e16275 b5e11745
            | (have j1 := b5e16275 X0
               grind)
            | exact resolve b5e11745 b5e16275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11745 b5e16275
          have b5e48009 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e47761 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47761
          have b5e55478 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e15991 (σ X0) X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e15991
            | (have j0 := b5e15991 (σ X0) X1
               grind)
            | exact resolve b5e15991 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15991
          have b5e55732 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e55478 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e55478
            | (have j0 := b5e55478 X0 X1
               grind)
            | exact resolve b5e55478 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55478
          have b5e55758 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e55732 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e55732
            | (have j0 := b5e55732 X0 X1
               grind)
            | exact resolve b5e55732 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55732
          have b5e57013 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e32 X0 y
               have i₂ := b5e20169 X0
               grind)
            | exact superpose b5e20169 b5e32
            | (have j1 := b5e20169 X0
               grind)
            | exact resolve b5e32 b5e20169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e20169
          have b5e73905 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (M.op X1 (k (σ (τ X0)) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e48009 (τ X0) X1
               have i₂ := b5e116 X0 (τ X0)
               grind)
            | exact superpose b5e116 b5e48009
            | (have j0 := b5e48009 (τ X0) X1
               have j1 := b5e116 X0 (τ X0)
               grind)
            | exact resolve b5e48009 b5e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116 b5e48009
          have b5e74147 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (M.op X1 (k (σ (τ X0)) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e73905 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73905
          have b5e74197 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e74147 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e74147
            | (have j0 := b5e74147 X0 X1
               grind)
            | exact resolve b5e74147 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74147
          have b5e84625 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e222 X0
               have i₂ := b5e55758 X0 X0
               grind)
            | exact superpose b5e55758 b5e222
            | (have j0 := b5e222 X0
               have j1 := b5e55758 X0 X0
               grind)
            | (have r₁ := b5e222 x
               have r₂ := b5e55758 x x
               grind)
            | exact resolve b5e222 b5e55758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55758
          have b5e84999 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e84625 X0
               have j1 := b5e222 X0
               grind)
            | (have r₁ := b5e84625 X0
               have r₂ := b5e222 X0
               grind)
            | exact resolve b5e84625 b5e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e222 b5e84625
          have b5e315158 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X1 X0) = (M.op X1 (k X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e84999 (τ X0)
               have i₂ := b5e74197 X0 X1
               grind)
            | exact superpose b5e74197 b5e84999
            | (have j0 := b5e84999 (τ X0)
               have j1 := b5e74197 X0 X1
               grind)
            | exact resolve b5e84999 b5e74197
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74197 b5e84999
          have b5e315216 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X1 X0) = (M.op X1 (k X0 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e315158 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e315158
          have b5e315240 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e315216 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e315216
            | (have j0 := b5e315216 X0 X1
               grind)
            | exact resolve b5e315216 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e315216
          have b5e316092 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e29066 X0
               have i₂ := b5e315240 X0 (k X0 X0)
               grind)
            | exact superpose b5e315240 b5e29066
            | (have j0 := b5e29066 X0
               have j1 := b5e315240 X0 x
               grind)
            | exact resolve b5e29066 b5e315240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29066 b5e315240
          have b5e316101 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e316092 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e316092
          have b5e316769 : ∀ X0 : G, (k X0 (M.op (k X0 X0) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e5706 X0 (k X0 X0)
               have i₂ := b5e316101 X0
               grind)
            | exact superpose b5e316101 b5e5706
            | (have j1 := b5e316101 X0
               grind)
            | exact resolve b5e5706 b5e316101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5706 b5e316101
          have b5e316884 : ∀ X0 : G, (k X0 (M.op (k X0 X0) X0)) = X0 := by
            intro X0
            first
            | (have j0 := b5e316769 X0
               have j1 := b5e81 X0 X0 (k X0 X0)
               grind)
            | (have r₁ := b5e316769 x
               have r₂ := b5e81 x x x
               grind)
            | exact resolve b5e316769 b5e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81 b5e316769
          have b5e317472 : ∀ X0 : G, (σ X0) = (k (σ X0) (M.op (σ (k X0 X0)) (σ X0))) := by
            intro X0
            first
            | (have i₁ := b5e316884 (σ X0)
               have i₂ := b5e19 X0 X0
               grind)
            | exact superpose b5e19 b5e316884
            | exact resolve b5e316884 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e316884
          have b5e484815 : (σ (k (M.op x x) y)) = (σ (k x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e5409 x x y
               have i₂ := b5e39950
               grind)
            | exact superpose b5e39950 b5e5409
            | (have j0 := b5e5409 x x x
               grind)
            | exact resolve b5e5409 b5e39950
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5409 b5e39950
          have b5e484841 : (σ (k (M.op x x) y)) = (σ (k x x)) ∨ x = (M.op x x) := by grind
          clear b5e484815
          have b5e484866 : (σ (k (M.op x x) y)) = (σ (k x x)) := by
            first
            | (have r₁ := b5e484841
               have r₂ := b5e65
               grind)
            | exact resolve b5e484841 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e484841
          have b5e484888 : (σ (M.op x x)) = (σ (k x x)) := by
            first
            | (have i₁ := b5e484866
               have i₂ := b5e315 x
               grind)
            | exact superpose b5e315 b5e484866
            | exact resolve b5e484866 b5e315
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e484866
          have b5e484947 : (σ x) = (k (σ x) (M.op (σ (M.op x x)) (σ x))) := by
            first
            | (have i₁ := b5e317472 x
               have i₂ := b5e484888
               grind)
            | exact superpose b5e484888 b5e317472
            | exact resolve b5e317472 b5e484888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e317472
          have b5e488956 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e45998 X0 X0
               have i₂ := b5e477 X0
               grind)
            | exact superpose b5e477 b5e45998
            | (have j0 := b5e45998 X0 X0
               grind)
            | exact resolve b5e45998 b5e477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45998
          have b5e500751 : (σ x) = (k (σ x) (σ (k x (M.op x x)))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b5e484947
               have i₂ := b5e2635 x x
               grind)
            | exact superpose b5e2635 b5e484947
            | (have j1 := b5e2635 x x
               grind)
            | exact resolve b5e484947 b5e2635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2635 b5e484947
          have b5e500763 : (σ x) = (σ (k x (k x (M.op x x)))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b5e500751
               have i₂ := b5e19 x (k x (M.op x x))
               grind)
            | exact superpose b5e19 b5e500751
            | exact resolve b5e500751 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e500751
          have b5e500770 : (σ x) = (σ (k x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b5e500763
               have i₂ := b5e477 x
               grind)
            | exact superpose b5e477 b5e500763
            | exact resolve b5e500763 b5e477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e477 b5e500763
          have b5e500774 : (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b5e500770
               have i₂ := b5e484888
               grind)
            | exact superpose b5e484888 b5e500770
            | exact resolve b5e500770 b5e484888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e484888 b5e500770
          have b5e500777 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have j1 := b5e488956 x
               grind)
            | (have r₁ := b5e500774
               have r₂ := b5e488956 x
               grind)
            | exact resolve b5e500774 b5e488956
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e488956 b5e500774
          have b5e500842 : ∀ X0 : G, (M.op X0 (σ (M.op x x))) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e37 (σ x) X0 (σ (M.op x x))
               have i₂ := b5e500777
               grind)
            | exact superpose b5e500777 b5e37
            | exact resolve b5e37 b5e500777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e500777
          have b5e501219 : (M.op (σ y) (σ x)) = (σ (k (M.op x x) y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e1851 (M.op x x)
               have i₂ := b5e500842 (σ y)
               grind)
            | exact superpose b5e500842 b5e1851
            | (have j0 := b5e1851 x
               grind)
            | exact resolve b5e1851 b5e500842
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1851 b5e500842
          have b5e501325 : (M.op (σ y) (σ x)) = (σ (k (M.op x x) y)) := by
            first
            | (have r₁ := b5e501219
               have r₂ := b5e24
               grind)
            | exact resolve b5e501219 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e501219
          have b5e501412 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e501325
               have i₂ := b5e315 x
               grind)
            | exact superpose b5e315 b5e501325
            | exact resolve b5e501325 b5e315
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e315 b5e501325
          have b5e501497 : (k (τ (σ x)) y) = (τ (σ (M.op x x))) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e57013 (σ x)
               have i₂ := b5e501412
               grind)
            | exact superpose b5e501412 b5e57013
            | exact resolve b5e57013 b5e501412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57013 b5e501412
          have b5e501697 : (k (τ (σ x)) y) = (τ (σ (M.op x x))) := by
            first
            | (have r₁ := b5e501497
               have r₂ := b5e259
               grind)
            | exact resolve b5e501497 b5e259
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e259 b5e501497
          have b5e501771 : (M.op x x) = (k (τ (σ x)) y) := by
            first
            | (have i₁ := b5e501697
               have i₂ := b5e14 (M.op x x)
               grind)
            | exact superpose b5e14 b5e501697
            | exact resolve b5e501697 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e501697
          have b5e501819 : (k x y) = (M.op x x) := by
            first
            | (have i₁ := b5e501771
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e501771
            | exact resolve b5e501771 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e501771
          have b5e501846 : x = (M.op x x) := by
            first
            | (have i₁ := b5e501819
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e501819
            | exact resolve b5e501819 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e501819
          have b5e501860 : False := by grind
          exact b5e501860
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e24 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
        have b6e35 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 X1)) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 (M.op X0 X0) X1 X2
             have i₂ := b6e12 X0 X0 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 (M.op X3 X1) (M.op X0 X0)
             have i₂ := b6e12 X0 X1 X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 (M.op X0 X0) (M.op X2 X1)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 (M.op X0 X0) (M.op X2 X1)
             grind)
          | (have r₁ := b6e15 (M.op X1 X1) (M.op X2 X1)
             have r₂ := b6e12 X1 X1 X2
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
          intro X1 X2 X3
          first
          | (have i₁ := b6e37 x X1 X2 X3
             have i₂ := b6e12 X2 X1 x
             grind)
          | exact superpose b6e12 b6e37
          | exact resolve b6e37 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e40 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e35 X0 X1 x
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e35
          | exact resolve b6e35 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e41 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e22
             grind)
          | exact resolve b6e16 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X0 X0)) ∨ (M.op X2 X1) = (k (M.op X2 X1) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 (M.op X2 X1) (M.op X0 X0)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e16
          | (have j0 := b6e16 (M.op X2 X1) (M.op X0 X0)
             grind)
          | (have r₁ := b6e16 (M.op X2 X1) (M.op X1 X1)
             have r₂ := b6e12 X1 X1 X2
             grind)
          | exact resolve b6e16 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        clear b6e41
        have b6e44 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X2 X1) = (k (M.op X2 X1) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e42 X0 X1 X2
             have j1 := b6e15 (M.op X2 X1) (M.op X0 X0)
             grind)
          | (have r₁ := b6e42 X0 X1 X2
             have r₂ := b6e15 (M.op X2 X1) (M.op X0 X0)
             grind)
          | exact resolve b6e42 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e45 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have j1 := b6e15 (σ y) (σ x)
             grind)
          | (have r₁ := b6e43
             have r₂ := b6e15 (σ y) (σ x)
             grind)
          | exact resolve b6e43 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e46 : (σ y) = (σ (k y x)) := by
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
        have b6e49 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e46
             grind)
          | exact superpose b6e46 b6e13
          | exact resolve b6e13 b6e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e50 : y = (k y x) := by
          first
          | (have i₁ := b6e49
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e49
          | exact resolve b6e49 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e17 (σ X1) (σ X0)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X0) (σ X1)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e56 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
        have b6e57 : (σ x) = (σ (M.op y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
        have b6e60 : (σ x) = (σ (M.op y x)) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e57
             have r₂ := b6e21
             grind)
          | exact resolve b6e57 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e61 : x = (M.op y x) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e56
             have r₂ := b6e21
             grind)
          | exact resolve b6e56 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e64 : (σ x) = (σ (M.op y x)) := by
          first
          | (have r₁ := b6e60
             have r₂ := b6e20
             grind)
          | exact resolve b6e60 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e65 : x = (M.op y x) := by
          first
          | (have r₁ := b6e61
             have r₂ := b6e20
             grind)
          | exact resolve b6e61 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e68 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e50
             grind)
          | exact superpose b6e50 b6e17
          | (have j0 := b6e17 y x
             grind)
          | exact resolve b6e17 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e69 : y = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e68
             have r₂ := b6e20
             grind)
          | exact resolve b6e68 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e71 : y = (M.op x y) := by
          first
          | (have r₁ := b6e69
             have r₂ := b6e21
             grind)
          | exact resolve b6e69 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e73 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e39 (σ y) X0 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e39
          | exact resolve b6e39 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e77 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X2 X1) = (M.op (M.op X2 X1) X0) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 (M.op X2 X1) X0
             have i₂ := b6e39 X1 X0 X2
             grind)
          | exact superpose b6e39 b6e16
          | (have j0 := b6e16 (M.op X2 X1) X0
             grind)
          | exact resolve b6e16 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e79 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X0 (M.op X2 X1)
             have i₂ := b6e39 X1 X0 X2
             grind)
          | exact superpose b6e39 b6e15
          | (have j0 := b6e15 X0 X1
             grind)
          | exact resolve b6e15 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e80 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op X0 X1) X2 X3
             have i₂ := b6e39 X1 (M.op X0 X1) X0
             grind)
          | exact superpose b6e39 b6e12
          | exact resolve b6e12 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e82 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e80 X0 X1 X2 x
             have i₂ := b6e39 X2 (M.op (M.op X0 X1) X1) x
             grind)
          | exact superpose b6e39 b6e80
          | exact resolve b6e80 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e84 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e77 X0 X1 X2
             have j1 := b6e15 X0 X1
             grind)
          | (have r₁ := b6e77 X1 X1 X2
             have r₂ := b6e15 (M.op X2 X1) X1
             grind)
          | exact resolve b6e77 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e97 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X1 (M.op X0 X0)
             have i₂ := b6e40 X0 X1
             grind)
          | exact superpose b6e40 b6e16
          | (have j0 := b6e16 X1 (M.op X0 X0)
             grind)
          | (have r₁ := b6e16 X1 (M.op X1 X1)
             have r₂ := b6e40 X1 X1
             grind)
          | exact resolve b6e16 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e104 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e97 X0 X1
             have j1 := b6e15 X1 (M.op X0 X0)
             grind)
          | (have r₁ := b6e97 X0 X0
             have r₂ := b6e15 X0 (M.op X0 X0)
             grind)
          | exact resolve b6e97 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e110 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e27 X0 X1
             grind)
          | exact superpose b6e27 b6e13
          | exact resolve b6e13 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e111 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e71
             grind)
          | exact superpose b6e71 b6e23
          | exact resolve b6e23 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e122 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e28 X1 X0
             grind)
          | exact superpose b6e28 b6e13
          | exact resolve b6e13 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e181 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e44 X1 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e206 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e73 (σ x)
             grind)
          | exact superpose b6e73 b6e22
          | exact resolve b6e22 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e255 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 (σ X1) (σ X0)
             have i₂ := b6e55 X1 X0
             grind)
          | exact superpose b6e55 b6e15
          | (have j0 := b6e15 (σ X1) (σ X0)
             have j1 := b6e55 X1 X0
             grind)
          | (have r₁ := b6e15 (σ X1) (σ X0)
             have r₂ := b6e55 X0 X1
             grind)
          | (have r₁ := b6e15 (σ X0) (σ X1)
             have r₂ := b6e55 X0 X1
             grind)
          | exact resolve b6e15 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e259 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (M.op X1 (σ X2)) = (M.op X1 (σ X0)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e39 (σ X2) X1 (σ X0)
             have i₂ := b6e55 X2 X0
             grind)
          | exact superpose b6e55 b6e39
          | (have j1 := b6e55 X2 X0
             grind)
          | exact resolve b6e39 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e260 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 (σ X1) (σ X0)
             have i₂ := b6e55 X1 X0
             grind)
          | exact superpose b6e55 b6e16
          | (have j0 := b6e16 (σ X1) (σ X0)
             have j1 := b6e55 X1 X0
             grind)
          | (have r₁ := b6e16 (σ X0) (σ X1)
             have r₂ := b6e55 X0 X1
             grind)
          | (have r₁ := b6e16 (σ X1) (σ X0)
             have r₂ := b6e55 X0 X1
             grind)
          | exact resolve b6e16 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e262 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 (σ X0) (σ X1)
             have i₂ := b6e55 X1 X0
             grind)
          | exact superpose b6e55 b6e15
          | (have j0 := b6e15 (σ X0) (σ X1)
             have j1 := b6e55 X1 X0
             grind)
          | (have r₁ := b6e15 (σ X1) (σ X0)
             have r₂ := b6e55 X0 X1
             grind)
          | (have r₁ := b6e15 (σ X0) (σ X1)
             have r₂ := b6e55 X0 X1
             grind)
          | exact resolve b6e15 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e263 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e55 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e264 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e265 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e263 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e263
        have b6e266 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e262 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e262
        have b6e267 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e260 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e260
        have b6e268 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e267 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e267
        have b6e276 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e266 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e266
          | (have j0 := b6e266 X0 X1
             grind)
          | exact resolve b6e266 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e266
        have b6e278 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e268 X0 X1
             have j1 := b6e15 (σ X1) (σ X0)
             grind)
          | (have r₁ := b6e268 X0 X1
             have r₂ := b6e15 (σ X1) (σ X0)
             grind)
          | exact resolve b6e268 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e268
        have b6e279 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e255 X0 X1
             have j1 := b6e16 (σ X1) (σ X0)
             grind)
          | (have r₁ := b6e255 X0 X1
             have r₂ := b6e16 (σ X1) (σ X0)
             grind)
          | (have r₁ := b6e255 X0 X1
             have r₂ := b6e16 (σ X0) (σ X1)
             grind)
          | exact resolve b6e255 b6e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e255
        have b6e304 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e278 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e278
          | (have j0 := b6e278 X0 X1
             grind)
          | exact resolve b6e278 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e278
        have b6e305 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e279 X0 X1
             have j1 := b6e15 (σ X1) (σ X0)
             grind)
          | (have r₁ := b6e279 X0 X1
             have r₂ := b6e15 (σ X1) (σ X0)
             grind)
          | exact resolve b6e279 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e279
        have b6e312 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e305 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e305
          | (have j0 := b6e305 X0 X1
             grind)
          | exact resolve b6e305 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e305
        have b6e322 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e44 (σ x) (σ x) x
             have i₂ := b6e206
             grind)
          | exact superpose b6e206 b6e44
          | exact resolve b6e44 b6e206
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e323 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b6e38 (σ x) (σ x) x
             have i₂ := b6e206
             grind)
          | exact superpose b6e206 b6e38
          | exact resolve b6e38 b6e206
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e325 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e206
             grind)
          | exact superpose b6e206 b6e15
          | (have j0 := b6e15 (σ x) (σ x)
             grind)
          | (have r₁ := b6e15 (σ x) (σ x)
             have r₂ := b6e206
             grind)
          | exact resolve b6e15 b6e206
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e326 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b6e325
        have b6e327 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have j0 := b6e323 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e323
        have b6e328 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (σ x)) := by
          intro X0
          first
          | (have j0 := b6e322 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e322
        have b6e330 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e326
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e326
          | exact resolve b6e326 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e326
        have b6e331 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e110 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e110
          | exact resolve b6e110 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e338 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e110 X1 X0
             have i₂ := b6e17 X1 (σ X0)
             grind)
          | exact superpose b6e17 b6e110
          | (have j1 := b6e17 X1 (σ X0)
             grind)
          | exact resolve b6e110 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e349 : (τ (σ x)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e330
             grind)
          | exact superpose b6e330 b6e13
          | exact resolve b6e13 b6e330
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e330
        have b6e361 : x = (k x x) := by
          first
          | (have i₁ := b6e349
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e349
          | exact resolve b6e349 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e349
        have b6e371 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e122 X1 X0
             have i₂ := b6e17 (σ X1) X0
             grind)
          | exact superpose b6e17 b6e122
          | (have j1 := b6e17 (σ X1) X0
             grind)
          | exact resolve b6e122 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e386 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e361
             grind)
          | exact superpose b6e361 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e361
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e361
        have b6e387 : x = (M.op x x) := by grind
        clear b6e386
        have b6e527 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X2 (M.op (M.op X0 X1) X1)) = X2 ∨ (k X2 (M.op (M.op X0 X1) X1)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 X2 (M.op (M.op X0 X1) X1)
             have i₂ := b6e82 X0 X1 X2
             grind)
          | exact superpose b6e82 b6e16
          | (have j0 := b6e16 X2 (M.op (M.op X0 X1) X1)
             grind)
          | (have r₁ := b6e16 X2 (M.op (M.op X0 X2) X2)
             have r₂ := b6e82 X0 X2 X2
             grind)
          | exact resolve b6e16 b6e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e541 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X2) ∨ (k X2 (M.op (M.op X0 X1) X1)) = X2 := by
          intro X0 X1 X2
          first
          | (have j0 := b6e527 X0 X1 X2
             have j1 := b6e15 X2 (M.op (M.op X0 X1) X1)
             grind)
          | (have r₁ := b6e527 X0 X1 X0
             have r₂ := b6e15 X0 (M.op (M.op X0 X1) X1)
             grind)
          | exact resolve b6e527 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e527
        have b6e581 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op X2 (σ X0)) = (k (M.op X2 (σ X0)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e84 (σ X1) (σ X0) X2
             have i₂ := b6e55 X1 X0
             grind)
          | exact superpose b6e55 b6e84
          | (have j0 := b6e84 (σ X1) (σ X0) X2
             have j1 := b6e55 X1 X0
             grind)
          | (have r₁ := b6e84 (σ X1) (σ X0) X2
             have r₂ := b6e55 X0 X1
             grind)
          | (have r₁ := b6e84 (σ X0) (σ X1) X2
             have r₂ := b6e55 X0 X1
             grind)
          | exact resolve b6e84 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e589 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op X2 (σ X0)) = (k (M.op X2 (σ X0)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e581 X0 X1 X2
             have j1 := b6e84 (σ X1) (σ X0) X2
             grind)
          | (have r₁ := b6e581 X0 X1 X2
             have r₂ := b6e84 (σ X0) (σ X1) X2
             grind)
          | (have r₁ := b6e581 X0 X1 X2
             have r₂ := b6e84 (σ X1) (σ X0) X2
             grind)
          | exact resolve b6e581 b6e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e581
        have b6e619 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (k X0 (M.op (σ y) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e104 (σ y) x
             have i₂ := b6e73 (σ y)
             grind)
          | exact superpose b6e73 b6e104
          | (have r₁ := b6e104 (σ x) (σ y)
             have r₂ := b6e73 (σ x)
             grind)
          | (have r₁ := b6e104 (σ y) (σ x)
             have r₂ := b6e73 (σ y)
             grind)
          | exact resolve b6e104 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e623 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e104 (σ x) x
             have i₂ := b6e206
             grind)
          | exact superpose b6e206 b6e104
          | exact resolve b6e104 b6e206
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104 b6e206
        have b6e752 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b6e122 x (M.op X0 (σ x))
             have i₂ := b6e327 X0
             grind)
          | exact superpose b6e327 b6e122
          | exact resolve b6e122 b6e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e756 : ∀ X0 : G, x = (k x (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b6e752 X0
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e752
          | exact resolve b6e752 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e752
        have b6e1017 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b6e265 (M.op X0 X0)
             have i₂ := b6e181 X0 X0
             grind)
          | exact superpose b6e181 b6e265
          | (have j0 := b6e265 (M.op X0 X0)
             grind)
          | exact resolve b6e265 b6e181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e181
        have b6e1022 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e265 (τ X0)
             have i₂ := b6e27 X0 (τ X0)
             grind)
          | exact superpose b6e27 b6e265
          | (have j0 := b6e265 (τ X0)
             grind)
          | exact resolve b6e265 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e265
        have b6e1026 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have j0 := b6e1017 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1017
        have b6e1029 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e1022 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1022
          | (have j0 := b6e1022 X0
             grind)
          | exact resolve b6e1022 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1022
        have b6e1032 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e1029 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1029
          | (have j0 := b6e1029 X0
             grind)
          | exact resolve b6e1029 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1029
        have b6e1040 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e1032 (τ X0)
             have i₂ := b6e331 X0 X0
             grind)
          | exact superpose b6e331 b6e1032
          | (have j0 := b6e1032 (τ X0)
             grind)
          | exact resolve b6e1032 b6e331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1032
        have b6e1112 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e304 X0 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e304
          | exact resolve b6e304 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e304
        have b6e1186 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e1112 X0 X1
             have i₂ := b6e28 X0 X1
             grind)
          | exact superpose b6e28 b6e1112
          | (have j0 := b6e1112 X0 X1
             grind)
          | exact resolve b6e1112 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1112
        have b6e1198 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e1186 X0 X1
             have i₂ := b6e27 X0 X1
             grind)
          | exact superpose b6e27 b6e1186
          | (have j0 := b6e1186 X0 X1
             grind)
          | exact resolve b6e1186 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1186
        have b6e1417 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e264 (τ X1) (τ X0)
             have i₂ := b6e331 X1 X0
             grind)
          | exact superpose b6e331 b6e264
          | (have j0 := b6e264 (τ X1) (τ X0)
             grind)
          | exact resolve b6e264 b6e331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1441 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e1417 X0 X1
             have i₂ := b6e14 (k X0 X1)
             grind)
          | exact superpose b6e14 b6e1417
          | (have j0 := b6e1417 X0 X1
             grind)
          | exact resolve b6e1417 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1417
        have b6e1448 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e1441 X0 X1
             have i₂ := b6e14 X1
             grind)
          | exact superpose b6e14 b6e1441
          | (have j0 := b6e1441 X0 X1
             grind)
          | exact resolve b6e1441 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1441
        have b6e1453 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e1448 X0 X1
             have i₂ := b6e14 X1
             grind)
          | exact superpose b6e14 b6e1448
          | (have j0 := b6e1448 X0 X1
             grind)
          | exact resolve b6e1448 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1448
        have b6e1455 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e1453 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1453
          | (have j0 := b6e1453 X0 X1
             grind)
          | exact resolve b6e1453 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1453
        have b6e1456 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e1455 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1455
          | (have j0 := b6e1455 X0 X1
             grind)
          | exact resolve b6e1455 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1455
        have b6e1457 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e1456 X0 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1456
          | (have j0 := b6e1456 X0 X1
             grind)
          | exact resolve b6e1456 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1456
        have b6e1623 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e276 (τ X0) X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e276
          | exact resolve b6e276 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e276
        have b6e1691 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e1623 X0 X1
             have i₂ := b6e27 X0 X1
             grind)
          | exact superpose b6e27 b6e1623
          | (have j0 := b6e1623 X0 X1
             grind)
          | exact resolve b6e1623 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1623
        have b6e1711 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e1691 X0 X1
             have i₂ := b6e27 X0 X1
             grind)
          | exact superpose b6e27 b6e1691
          | (have j0 := b6e1691 X0 X1
             grind)
          | exact resolve b6e1691 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1691
        have b6e2092 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (σ X2)) ∨ (σ (k X2 (τ X0))) = (M.op X0 (σ X2)) ∨ (M.op X0 (σ X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e259 X0 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e259
          | exact resolve b6e259 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2119 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (σ X2)) ∨ (σ (k (τ X0) X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (M.op (σ X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e259 (τ X0) X1 X2
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e259
          | exact resolve b6e259 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2264 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ X0)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e22
             have i₂ := b6e259 y (σ x) X0
             grind)
          | (have i₁ := b6e22
             have i₂ := b6e259 X0 (σ x) y
             grind)
          | exact superpose b6e259 b6e22
          | (have j1 := b6e259 y x X0
             grind)
          | exact resolve b6e22 b6e259
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2276 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e259 X0 (σ X0) X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2277 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (M.op X2 (σ X0)) = (M.op X2 (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e259 X1 X2 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e259
        have b6e2282 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e2264 X0
             have i₂ := b6e73 (σ X0)
             grind)
          | exact superpose b6e73 b6e2264
          | (have j0 := b6e2264 X0
             grind)
          | exact resolve b6e2264 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2264
        have b6e2325 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (M.op X1 X0) = (M.op X1 (σ X2)) ∨ (σ X2) = (M.op (σ X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e2119 X0 X1 X2
             have i₂ := b6e27 X0 X2
             grind)
          | exact superpose b6e27 b6e2119
          | (have j0 := b6e2119 X0 X1 X2
             grind)
          | exact resolve b6e2119 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2119
        have b6e2336 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (k (σ X2) X0) ∨ (M.op X1 X0) = (M.op X1 (σ X2)) ∨ (M.op X0 (σ X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e2092 X0 X1 X2
             have i₂ := b6e28 X0 X2
             grind)
          | exact superpose b6e28 b6e2092
          | (have j0 := b6e2092 X0 X1 X2
             grind)
          | exact resolve b6e2092 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2092
        have b6e2354 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e2282 X0
             have i₂ := b6e73 (σ X0)
             grind)
          | exact superpose b6e73 b6e2282
          | (have j0 := b6e2282 X0
             grind)
          | exact resolve b6e2282 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2282
        have b6e2489 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ (M.op X0 (σ x))) x) := by
          intro X0
          first
          | (have i₁ := b6e110 (M.op X0 (σ x)) x
             have i₂ := b6e328 X0
             grind)
          | exact superpose b6e328 b6e110
          | exact resolve b6e110 b6e328
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e328
        have b6e5127 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e1198 X0 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1198
          | exact resolve b6e1198 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e5163 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e122 X0 (σ X1)
             have i₂ := b6e1198 (σ X0) X1
             grind)
          | exact superpose b6e1198 b6e122
          | (have j1 := b6e1198 (σ X0) X1
             grind)
          | exact resolve b6e122 b6e1198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1198
        have b6e5247 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e5163 X0 X1
             have i₂ := b6e13 X1
             grind)
          | exact superpose b6e13 b6e5163
          | (have j0 := b6e5163 X0 X1
             grind)
          | exact resolve b6e5163 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5163
        have b6e5277 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e5247 X0 X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e5247
          | (have j0 := b6e5247 X0 X1
             grind)
          | exact resolve b6e5247 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5247
        have b6e5286 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e5277 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e5277
          | (have j0 := b6e5277 X0 X1
             grind)
          | exact resolve b6e5277 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5277
        have b6e5413 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e122 X0 X1
             have i₂ := b6e5127 X1 (σ X0)
             grind)
          | exact superpose b6e5127 b6e122
          | (have j1 := b6e5127 X1 (σ X0)
             grind)
          | exact resolve b6e122 b6e5127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e5422 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e27 X0 X1
             have i₂ := b6e5127 X1 (τ X0)
             grind)
          | exact superpose b6e5127 b6e27
          | (have j1 := b6e5127 X1 (τ X0)
             grind)
          | exact resolve b6e27 b6e5127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e5445 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e5422 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e5422
          | (have j0 := b6e5422 X0 X1
             grind)
          | exact resolve b6e5422 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5422
        have b6e5452 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e5413 X0 X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e5413
          | (have j0 := b6e5413 X0 X1
             grind)
          | exact resolve b6e5413 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5413
        have b6e7377 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) X0)) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e541 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e541
        have b6e14284 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e1711 X0 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1711
          | exact resolve b6e1711 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e14318 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e1711 X0 (M.op y x)
             have i₂ := b6e64
             grind)
          | exact superpose b6e64 b6e1711
          | (have j0 := b6e1711 X0 x
             grind)
          | exact resolve b6e1711 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1711
        have b6e14441 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have j0 := b6e14318 X0
             have j1 := b6e623 X0
             grind)
          | (have r₁ := b6e14318 X0
             have r₂ := b6e623 X0
             grind)
          | exact resolve b6e14318 b6e623
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e623 b6e14318
        have b6e15109 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e338 (τ X0) X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e338
          | exact resolve b6e338 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e338
        have b6e15242 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e15109 X0 X1
             have i₂ := b6e331 X0 X1
             grind)
          | exact superpose b6e331 b6e15109
          | (have j0 := b6e15109 X0 X1
             grind)
          | exact resolve b6e15109 b6e331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15109
        have b6e15663 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ x)) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e73 (σ X0)
             have i₂ := b6e5286 X0 y
             grind)
          | exact superpose b6e5286 b6e73
          | (have j1 := b6e5286 X0 y
             grind)
          | exact resolve b6e73 b6e5286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5286
        have b6e17561 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op X0 (σ y)) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e22
             have i₂ := b6e2336 X0 (σ x) y
             grind)
          | (have i₁ := b6e22
             have i₂ := b6e2336 (σ y) (σ x) x
             grind)
          | exact superpose b6e2336 b6e22
          | (have j1 := b6e2336 X0 x y
             grind)
          | exact resolve b6e22 b6e2336
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e17585 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e2336 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2336
        have b6e17605 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e17561 X0
             have i₂ := b6e73 X0
             grind)
          | exact superpose b6e73 b6e17561
          | (have j0 := b6e17561 X0
             grind)
          | exact resolve b6e17561 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17561
        have b6e17745 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ y) X0) ∨ (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e17605 X0
             have i₂ := b6e73 X0
             grind)
          | exact superpose b6e73 b6e17605
          | (have j0 := b6e17605 X0
             grind)
          | exact resolve b6e17605 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17605
        have b6e18972 : ∀ X0 : G, (M.op (σ x) X0) ≠ X0 ∨ (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have j0 := b6e14441 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e14441
        have b6e20952 : ∀ X0 X1 X2 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e2277 (τ X1) (τ X0) X2
             have i₂ := b6e331 X1 X0
             grind)
          | exact superpose b6e331 b6e2277
          | (have j0 := b6e2277 (τ X0) (τ X1) X2
             grind)
          | exact resolve b6e2277 b6e331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e331 b6e2277
        have b6e21042 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e20952 X0 X1 X2
             have i₂ := b6e14 (k X0 X1)
             grind)
          | exact superpose b6e14 b6e20952
          | (have j0 := b6e20952 X0 X1 X2
             grind)
          | exact resolve b6e20952 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e20952
        have b6e21083 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X1 ∨ (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e21042 X0 X1 X2
             have i₂ := b6e14 X1
             grind)
          | exact superpose b6e14 b6e21042
          | (have j0 := b6e21042 X0 X1 X2
             grind)
          | exact resolve b6e21042 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e21042
        have b6e21110 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (σ (τ X0))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e21083 X0 X1 X2
             have i₂ := b6e14 X1
             grind)
          | exact superpose b6e14 b6e21083
          | (have j0 := b6e21083 X0 X1 X2
             grind)
          | exact resolve b6e21083 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e21083
        have b6e21126 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e21110 X0 X1 X2
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e21110
          | (have j0 := b6e21110 X0 X1 X2
             grind)
          | exact resolve b6e21110 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e21110
        have b6e21136 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 X1) = (M.op X2 X0) ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e21126 X0 X1 X2
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e21126
          | (have j0 := b6e21126 X0 X1 X2
             grind)
          | exact resolve b6e21126 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e21126
        have b6e21142 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X1 ∨ (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e21136 X0 X0 X2
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e21136
          | (have j0 := b6e21136 X0 X1 X2
             grind)
          | exact resolve b6e21136 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e21136
        have b6e21877 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) ∨ (M.op (σ (M.op X0 X0)) X1) = (k X1 (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e1026 X0
             have i₂ := b6e2325 X1 (σ (M.op X0 X0)) (M.op X0 X0)
             grind)
          | (have i₁ := b6e1026 X0
             have i₂ := b6e2325 (σ (M.op X0 X0)) (σ (M.op X0 X0)) x
             grind)
          | exact superpose b6e2325 b6e1026
          | (have j1 := b6e2325 X1 X1 (M.op X0 X0)
             grind)
          | exact resolve b6e1026 b6e2325
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2325
        have b6e21914 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (k X1 (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
          intro X0 X1
          first
          | (have j0 := b6e21877 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e21877
        have b6e22834 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
          intro X0
          first
          | (have i₁ := b6e1040 (σ X0)
             have i₂ := b6e5445 (σ X0) X0
             grind)
          | exact superpose b6e5445 b6e1040
          | (have j0 := b6e1040 (σ X0)
             have j1 := b6e5445 (σ X0) X0
             grind)
          | exact resolve b6e1040 b6e5445
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e22945 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) X1)) ∨ (σ (τ X0)) = (σ (k (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e312 X1 (τ X0)
             have i₂ := b6e5445 X0 X1
             grind)
          | exact superpose b6e5445 b6e312
          | (have j0 := b6e312 X1 (τ X0)
             have j1 := b6e5445 X0 X1
             grind)
          | exact resolve b6e312 b6e5445
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e312 b6e5445
        have b6e23011 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
          intro X0
          first
          | (have j0 := b6e22834 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e22834
        have b6e23051 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) ≠ X0 ∨ (σ (τ X0)) = (σ (k (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e22945 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e22945
          | (have j0 := b6e22945 X0 X1
             grind)
          | exact resolve b6e22945 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e22945
        have b6e23113 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
          intro X0
          first
          | (have i₁ := b6e23011 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e23011
          | (have j0 := b6e23011 X0
             grind)
          | exact resolve b6e23011 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23011
        have b6e23176 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (σ (M.op (τ X0) X1)) ≠ X0 ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e23051 X0 X1
             have i₂ := b6e27 X0 X1
             grind)
          | exact superpose b6e27 b6e23051
          | (have j0 := b6e23051 X0 X1
             grind)
          | exact resolve b6e23051 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23051
        have b6e23222 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e23113 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e23113
          | (have j0 := b6e23113 X0
             grind)
          | exact resolve b6e23113 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23113
        have b6e23245 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) ≠ X0 ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e23176 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e23176
          | (have j0 := b6e23176 X0 X1
             grind)
          | exact resolve b6e23176 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23176
        have b6e23246 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) ≠ X0 ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e23245 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23245
        have b6e25485 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e23246 (σ X0) X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e23246
          | (have j0 := b6e23246 (σ X0) X1
             grind)
          | exact resolve b6e23246 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23246
        have b6e25522 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e25485 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e25485
          | (have j0 := b6e25485 X0 X1
             grind)
          | exact resolve b6e25485 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25485
        have b6e27334 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 (M.op X2 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e25522 X0 (M.op X2 X1)
             have i₂ := b6e39 X1 X0 X2
             grind)
          | exact superpose b6e39 b6e25522
          | (have j0 := b6e25522 X0 X1
             grind)
          | exact resolve b6e25522 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25522
        have b6e27917 : ∀ X0 : G, (k x (τ (σ X0))) = (τ (σ (k y X0))) ∨ (σ X0) = (σ (k y X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e371 (σ X0) x
             have i₂ := b6e2354 X0
             grind)
          | exact superpose b6e2354 b6e371
          | (have j0 := b6e371 (σ x) X0
             have j1 := b6e2354 X0
             grind)
          | exact resolve b6e371 b6e2354
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e371
        have b6e27988 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (k (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e16 (σ X0) (σ x)
             have i₂ := b6e2354 X0
             grind)
          | exact superpose b6e2354 b6e16
          | (have j0 := b6e16 (σ X0) (σ x)
             have j1 := b6e2354 X0
             grind)
          | (have r₁ := b6e16 (σ X0) (σ x)
             have r₂ := b6e2354 X0
             grind)
          | (have r₁ := b6e16 (σ x) (σ X0)
             have r₂ := b6e2354 X0
             grind)
          | exact resolve b6e16 b6e2354
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28013 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b6e2354 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2354
        have b6e28018 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (k (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b6e27988 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27988
        have b6e28019 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (k (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b6e28018 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28018
        have b6e28043 : ∀ X0 : G, (k x (τ (σ X0))) = (τ (σ (k y X0))) ∨ (σ X0) = (σ (k y X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b6e27917 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27917
        have b6e28082 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b6e28019 X0
             have j1 := b6e15 (σ X0) (σ x)
             grind)
          | (have r₁ := b6e28019 X0
             have r₂ := b6e15 (σ X0) (σ x)
             grind)
          | exact resolve b6e28019 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28019
        have b6e28104 : ∀ X0 : G, (k x (τ (σ X0))) = (τ (σ (k y X0))) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b6e28043 X0
             have j1 := b6e28013 X0
             grind)
          | (have r₁ := b6e28043 X0
             have r₂ := b6e28013 X0
             grind)
          | exact resolve b6e28043 b6e28013
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28013 b6e28043
        have b6e28144 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e28082 X0
             have i₂ := b6e18 X0 x
             grind)
          | exact superpose b6e18 b6e28082
          | (have j0 := b6e28082 X0
             grind)
          | exact resolve b6e28082 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28082
        have b6e28153 : ∀ X0 : G, (k y X0) = (k x (τ (σ X0))) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e28104 X0
             have i₂ := b6e13 (k y X0)
             grind)
          | exact superpose b6e13 b6e28104
          | (have j0 := b6e28104 X0
             grind)
          | exact resolve b6e28104 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28104
        have b6e28164 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (k x X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b6e28153 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e28153
          | (have j0 := b6e28153 X0
             grind)
          | exact resolve b6e28153 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28153
        have b6e36152 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e122 X1 (σ X0)
             have i₂ := b6e5452 X0 (σ X1)
             grind)
          | exact superpose b6e5452 b6e122
          | (have j1 := b6e5452 X0 (σ X1)
             grind)
          | exact resolve b6e122 b6e5452
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e36228 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e36152 X0 X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e36152
          | (have j0 := b6e36152 X0 X1
             grind)
          | exact resolve b6e36152 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36152
        have b6e36350 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e36228 X0 X1
             have i₂ := b6e13 X1
             grind)
          | exact superpose b6e13 b6e36228
          | (have j0 := b6e36228 X0 X1
             grind)
          | exact resolve b6e36228 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36228
        have b6e40560 : ∀ X0 : G, (τ (σ (k y X0))) = (k (τ (σ (k y X0))) x) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e2489 (σ X0)
             have i₂ := b6e15663 X0
             grind)
          | exact superpose b6e15663 b6e2489
          | (have j1 := b6e15663 X0
             grind)
          | exact resolve b6e2489 b6e15663
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2489 b6e15663
        have b6e40643 : ∀ X0 : G, (k y X0) = (k (k y X0) x) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e40560 X0
             have i₂ := b6e13 (k y X0)
             grind)
          | exact superpose b6e13 b6e40560
          | (have j0 := b6e40560 X0
             grind)
          | exact resolve b6e40560 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40560
        have b6e41607 : (M.op y y) = (k (M.op y y) x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e40643 y
             have i₂ := b6e23222 y
             grind)
          | exact superpose b6e23222 b6e40643
          | (have j1 := b6e23222 y
             grind)
          | exact resolve b6e40643 b6e23222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23222 b6e40643
        have b6e41661 : (M.op y y) = (k (M.op y y) x) ∨ y = (M.op y y) := by grind
        clear b6e41607
        have b6e43894 : (M.op y y) = (M.op x (M.op y y)) ∨ x = (M.op x (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 (M.op y y) x
             have i₂ := b6e41661
             grind)
          | exact superpose b6e41661 b6e17
          | (have j0 := b6e17 (M.op y y) x
             grind)
          | exact resolve b6e17 b6e41661
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43917 : (M.op x y) = (M.op y y) ∨ x = (M.op x (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e43894
             have i₂ := b6e39 y x y
             grind)
          | exact superpose b6e39 b6e43894
          | exact resolve b6e43894 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43894
        have b6e43921 : y = (M.op y y) ∨ x = (M.op x (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e43917
             have i₂ := b6e71
             grind)
          | exact superpose b6e71 b6e43917
          | exact resolve b6e43917 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43917
        have b6e43922 : y = (M.op y y) ∨ x = (M.op x (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) x) := by grind
        clear b6e43921
        have b6e43926 : x = (M.op x y) ∨ y = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) x) := by
          first
          | (have i₁ := b6e43922
             have i₂ := b6e39 y x y
             grind)
          | exact superpose b6e39 b6e43922
          | exact resolve b6e43922 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43922
        have b6e43929 : y = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) x) := by
          first
          | (have r₁ := b6e43926
             have r₂ := b6e20
             grind)
          | exact resolve b6e43926 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43926
        have b6e43932 : (M.op y x) = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e43929
             have i₂ := b6e40 y x
             grind)
          | exact superpose b6e40 b6e43929
          | exact resolve b6e43929 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43929
        have b6e43935 : y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e43932
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e43932
          | exact resolve b6e43932 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43932
        have b6e48171 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e2276 (M.op X0 X0) X1
             have i₂ := b6e1026 X0
             grind)
          | exact superpose b6e1026 b6e2276
          | (have j0 := b6e2276 (M.op X0 X0) X1
             grind)
          | exact resolve b6e2276 b6e1026
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1026 b6e2276
        have b6e48202 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e48171 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48171
        have b6e348467 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e14284 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e14284
        have b6e351390 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e348467 (M.op x X1) X2
             have i₂ := b6e39 X1 X2 x
             grind)
          | exact superpose b6e39 b6e348467
          | (have j0 := b6e348467 (M.op X2 X1) X0
             grind)
          | (have r₁ := b6e348467 (M.op X2 X1) X2
             have r₂ := b6e39 X1 X2 X2
             grind)
          | exact resolve b6e348467 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e348467
        have b6e351453 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e351390 X0 X1 X2
             have j1 := b6e84 X0 X1 X2
             grind)
          | (have r₁ := b6e351390 X0 X1 X2
             have r₂ := b6e84 X0 X1 X2
             grind)
          | exact resolve b6e351390 b6e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e351390
        have b6e355599 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b6e351453 X0 x y
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e351453
          | exact resolve b6e351453 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e355601 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b6e351453 X0 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e387880 : ∀ X0 : G, x ≠ (M.op y y) ∨ (M.op X0 x) = (M.op X0 (M.op y y)) ∨ x = (M.op x (M.op y y)) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b6e21142 (M.op y y) x X0
             have i₂ := b6e41661
             grind)
          | exact superpose b6e41661 b6e21142
          | (have j0 := b6e21142 (M.op y y) x X0
             grind)
          | exact resolve b6e21142 b6e41661
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e21142 b6e41661
        have b6e387952 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y y)) ∨ x = (M.op x (M.op y y)) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have j0 := b6e387880 X0
             grind)
          | (have r₁ := b6e387880 X0
             have r₂ := b6e43935
             grind)
          | exact resolve b6e387880 b6e43935
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43935 b6e387880
        have b6e387961 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ x = (M.op x (M.op y y)) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b6e387952 X0
             have i₂ := b6e39 y X0 y
             grind)
          | exact superpose b6e39 b6e387952
          | exact resolve b6e387952 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e387952
        have b6e387967 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 x) = (M.op X0 y) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b6e387961 X0
             have i₂ := b6e39 y x y
             grind)
          | exact superpose b6e39 b6e387961
          | (have j0 := b6e387961 X0
             grind)
          | exact resolve b6e387961 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e387961
        have b6e387970 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have j0 := b6e387967 X0
             grind)
          | (have r₁ := b6e387967 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e387967 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e387967
        have b6e388719 : ∀ X0 : G, y = (k y (M.op (M.op X0 x) y)) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b6e7377 y X0
             have i₂ := b6e387970 X0
             grind)
          | exact superpose b6e387970 b6e7377
          | exact resolve b6e7377 b6e387970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7377 b6e387970
        have b6e388949 : ∀ X0 : G, y = (k y (M.op (M.op X0 x) y)) := by
          intro X0
          first
          | (have j0 := b6e388719 X0
             have j1 := b6e79 y y (M.op X0 x)
             grind)
          | (have r₁ := b6e388719 X0
             have r₂ := b6e79 y y x
             grind)
          | exact resolve b6e388719 b6e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79 b6e388719
        have b6e389666 : y = (k y (M.op x y)) := by
          first
          | (have i₁ := b6e388949 x
             have i₂ := b6e40 x y
             grind)
          | exact superpose b6e40 b6e388949
          | exact resolve b6e388949 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e388949
        have b6e389703 : y = (k y y) := by
          first
          | (have i₁ := b6e389666
             have i₂ := b6e71
             grind)
          | exact superpose b6e71 b6e389666
          | exact resolve b6e389666 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e389666
        have b6e390261 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
          first
          | (have i₁ := b6e1040 y
             have i₂ := b6e389703
             grind)
          | exact superpose b6e389703 b6e1040
          | (have j0 := b6e1040 y
             grind)
          | exact resolve b6e1040 b6e389703
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1040
        have b6e390284 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e264 y y
             have i₂ := b6e389703
             grind)
          | exact superpose b6e389703 b6e264
          | (have j0 := b6e264 y y
             grind)
          | exact resolve b6e264 b6e389703
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e264
        have b6e390288 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e589 y y X0
             have i₂ := b6e389703
             grind)
          | exact superpose b6e389703 b6e589
          | (have j0 := b6e589 y y X0
             grind)
          | exact resolve b6e589 b6e389703
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e589
        have b6e390290 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e1457 y y
             have i₂ := b6e389703
             grind)
          | exact superpose b6e389703 b6e1457
          | (have j0 := b6e1457 y y
             grind)
          | (have r₁ := b6e1457 y y
             have r₂ := b6e389703
             grind)
          | exact resolve b6e1457 b6e389703
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1457 b6e389703
        have b6e390291 : y ≠ y ∨ y = (M.op y y) := by grind
        clear b6e390290
        have b6e390292 : y = (M.op y y) := by grind
        clear b6e390291
        have b6e390294 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have j0 := b6e390288 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e390288
        have b6e390298 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b6e390284
        have b6e390299 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b6e390298
        have b6e390304 : (τ y) = (M.op (τ y) (τ y)) := by grind
        clear b6e390261
        have b6e390313 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op X0 (σ y)) (σ y)) := by
          intro X0
          first
          | (have j0 := b6e390294 X0
             have j1 := b6e84 (σ y) (σ y) X0
             grind)
          | (have r₁ := b6e390294 X0
             have r₂ := b6e84 (σ y) (σ y) x
             grind)
          | exact resolve b6e390294 b6e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84 b6e390294
        have b6e390316 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e390299
             have i₂ := b6e73 (σ y)
             grind)
          | exact superpose b6e73 b6e390299
          | exact resolve b6e390299 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e390299
        have b6e390324 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e390313 X0
             have i₂ := b6e73 X0
             grind)
          | exact superpose b6e73 b6e390313
          | exact resolve b6e390313 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73 b6e390313
        have b6e390918 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y (M.op X0 y))) := by
          intro X0
          first
          | (have i₁ := b6e27334 y y X0
             have i₂ := b6e390292
             grind)
          | exact superpose b6e390292 b6e27334
          | (have j0 := b6e27334 y y X0
             grind)
          | exact resolve b6e27334 b6e390292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27334 b6e390292
        have b6e390941 : ∀ X0 : G, (σ y) = (σ (k y (M.op X0 y))) := by
          intro X0
          first
          | (have j0 := b6e390918 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e390918
        have b6e392753 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e619 X0
             have i₂ := b6e390316
             grind)
          | exact superpose b6e390316 b6e619
          | exact resolve b6e619 b6e390316
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e619
        have b6e410952 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ (M.op X0 (σ x))) y) := by
          intro X0
          first
          | (have i₁ := b6e110 (M.op X0 (σ x)) y
             have i₂ := b6e390324 X0
             grind)
          | exact superpose b6e390324 b6e110
          | exact resolve b6e110 b6e390324
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e110 b6e390324
        have b6e423843 : ∀ X0 : G, (k x X0) = (k (k x X0) y) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b6e410952 (σ X0)
             have i₂ := b6e36350 X0 x
             grind)
          | exact superpose b6e36350 b6e410952
          | (have j1 := b6e36350 (k x X0) y
             grind)
          | exact resolve b6e410952 b6e36350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36350 b6e410952
        have b6e452930 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) y) ∨ (k X0 x) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b6e423843 x
             have i₂ := b6e5127 x x
             grind)
          | exact superpose b6e5127 b6e423843
          | (have j0 := b6e423843 X0
             have j1 := b6e5127 y (M.op X0 x)
             grind)
          | exact resolve b6e423843 b6e5127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e423843
        have b6e452979 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) y) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b6e452930 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e452930
        have b6e500232 : ∀ X0 : G, (M.op X0 (σ x)) = (σ (k y (τ X0))) ∨ (σ (k (τ X0) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e28144 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e28144
          | exact resolve b6e28144 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28144
        have b6e500455 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ y) X0) ∨ (σ (k (τ X0) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e500232 X0
             have i₂ := b6e28 X0 y
             grind)
          | exact superpose b6e28 b6e500232
          | (have j0 := b6e500232 X0
             grind)
          | exact resolve b6e500232 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e500232
        have b6e500479 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op X0 (σ x)) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e500455 X0
             have i₂ := b6e27 X0 x
             grind)
          | exact superpose b6e27 b6e500455
          | (have j0 := b6e500455 X0
             grind)
          | exact resolve b6e500455 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e500455
        have b6e503617 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e122 X0 (σ x)
             have i₂ := b6e500479 (σ X0)
             grind)
          | exact superpose b6e500479 b6e122
          | (have j1 := b6e500479 (σ X0)
             grind)
          | exact resolve b6e122 b6e500479
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e500479
        have b6e503744 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e503617 X0
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e503617
          | (have j0 := b6e503617 X0
             grind)
          | exact resolve b6e503617 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e503617
        have b6e503773 : ∀ X0 : G, (k X0 x) = X0 ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e503744 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e503744
          | (have j0 := b6e503744 X0
             grind)
          | exact resolve b6e503744 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e503744
        have b6e503788 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ x)) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b6e503773 X0
             have i₂ := b6e18 y X0
             grind)
          | exact superpose b6e18 b6e503773
          | (have j0 := b6e503773 X0
             grind)
          | exact resolve b6e503773 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e503773
        have b6e513146 : ∀ X0 : G, x ≠ x ∨ (M.op x (σ X0)) = (k (σ X0) x) ∨ x = (M.op x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e17585 x X0
             have i₂ := b6e387
             grind)
          | exact superpose b6e387 b6e17585
          | (have j0 := b6e17585 x X0
             grind)
          | (have r₁ := b6e17585 x x
             have r₂ := b6e387
             grind)
          | exact resolve b6e17585 b6e387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e387 b6e17585
        have b6e513156 : ∀ X0 : G, (M.op x (σ X0)) = (k (σ X0) x) ∨ x = (M.op x (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e513146 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e513146
        have b6e513282 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e513156 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e513156
          | exact resolve b6e513156 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e513156
        have b6e541980 : ∀ X0 : G, (σ x) = (k (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (k x X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b6e327 (σ X0)
             have i₂ := b6e28164 X0
             grind)
          | exact superpose b6e28164 b6e327
          | (have j1 := b6e28164 X0
             grind)
          | exact resolve b6e327 b6e28164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e327 b6e28164
        have b6e542014 : ∀ X0 : G, (σ x) = (k (σ x) (σ X0)) ∨ (k x X0) = (k y X0) := by
          intro X0
          first
          | (have j0 := b6e541980 X0
             have j1 := b6e15 (σ x) (σ X0)
             grind)
          | (have r₁ := b6e541980 X0
             have r₂ := b6e15 (σ x) (σ X0)
             grind)
          | exact resolve b6e541980 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e541980
        have b6e542023 : ∀ X0 : G, (σ x) = (σ (k x X0)) ∨ (k x X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b6e542014 X0
             have i₂ := b6e18 x X0
             grind)
          | exact superpose b6e18 b6e542014
          | (have j0 := b6e542014 X0
             grind)
          | exact resolve b6e542014 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e542014
        have b6e542078 : ∀ X0 : G, (τ (σ x)) = (k x X0) ∨ (k x X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b6e13 (k x X0)
             have i₂ := b6e542023 X0
             grind)
          | exact superpose b6e542023 b6e13
          | (have j1 := b6e542023 X0
             grind)
          | exact resolve b6e13 b6e542023
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e542023
        have b6e542166 : ∀ X0 : G, (k x X0) = (k y X0) ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b6e542078 X0
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e542078
          | (have j0 := b6e542078 X0
             grind)
          | exact resolve b6e542078 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e542078
        have b6e544669 : ∀ X0 : G, (σ (τ y)) ≠ (σ (k X0 (τ y))) ∨ (σ (τ y)) = (M.op (σ (τ y)) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e48202 (τ y) x
             have i₂ := b6e390304
             grind)
          | exact superpose b6e390304 b6e48202
          | exact resolve b6e48202 b6e390304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48202
        have b6e544709 : ∀ X0 : G, (k (σ X0) y) ≠ (σ (τ y)) ∨ (σ (τ y)) = (M.op (σ (τ y)) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e544669 X0
             have i₂ := b6e28 y X0
             grind)
          | exact superpose b6e28 b6e544669
          | (have j0 := b6e544669 X0
             grind)
          | exact resolve b6e544669 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e544669
        have b6e544719 : ∀ X0 : G, y ≠ (k (σ X0) y) ∨ (σ (τ y)) = (M.op (σ (τ y)) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e544709 X0
             have i₂ := b6e14 y
             grind)
          | exact superpose b6e14 b6e544709
          | (have j0 := b6e544709 X0
             grind)
          | exact resolve b6e544709 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e544709
        have b6e544728 : ∀ X0 : G, y ≠ (k (σ X0) y) ∨ y = (M.op y (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e544719 X0
             have i₂ := b6e14 y
             grind)
          | exact superpose b6e14 b6e544719
          | (have j0 := b6e544719 X0
             grind)
          | exact resolve b6e544719 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e544719
        have b6e545233 : ∀ X0 : G, y ≠ (k X0 y) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e544728 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e544728
          | exact resolve b6e544728 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e544728
        have b6e548946 : ∀ X0 : G, (M.op (σ (τ y)) X0) = (k X0 (σ (τ y))) ∨ (σ (τ y)) = (M.op (σ (τ y)) X0) := by
          intro X0
          first
          | (have i₁ := b6e21914 (τ y) x
             have i₂ := b6e390304
             grind)
          | exact superpose b6e390304 b6e21914
          | exact resolve b6e21914 b6e390304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e21914 b6e390304
        have b6e548971 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ (τ y)) = (M.op (σ (τ y)) X0) := by
          intro X0
          first
          | (have i₁ := b6e548946 X0
             have i₂ := b6e14 y
             grind)
          | exact superpose b6e14 b6e548946
          | (have j0 := b6e548946 X0
             grind)
          | exact resolve b6e548946 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e548946
        have b6e548977 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e548971 X0
             have i₂ := b6e14 y
             grind)
          | exact superpose b6e14 b6e548971
          | (have j0 := b6e548971 X0
             grind)
          | exact resolve b6e548971 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e548971
        have b6e549195 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op X0 x)) ∨ (k X0 x) = X0 ∨ y = (M.op y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e452979 X0
             have i₂ := b6e548977 (M.op X0 x)
             grind)
          | exact superpose b6e548977 b6e452979
          | (have j0 := b6e452979 X0
             have j1 := b6e548977 (M.op X0 x)
             grind)
          | exact resolve b6e452979 b6e548977
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e452979
        have b6e549628 : ∀ X0 : G, (M.op y x) = (M.op X0 x) ∨ (k X0 x) = X0 ∨ y = (M.op y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e549195 X0
             have i₂ := b6e39 x y X0
             grind)
          | exact superpose b6e39 b6e549195
          | (have j0 := b6e549195 X0
             grind)
          | exact resolve b6e549195 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e549195
        have b6e549682 : ∀ X0 : G, x = (M.op X0 x) ∨ (k X0 x) = X0 ∨ y = (M.op y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e549628 X0
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e549628
          | (have j0 := b6e549628 X0
             grind)
          | exact resolve b6e549628 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e549628
        have b6e549707 : ∀ X0 : G, y = (M.op y x) ∨ x = (M.op X0 x) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b6e549682 X0
             have i₂ := b6e39 x y X0
             grind)
          | exact superpose b6e39 b6e549682
          | (have j0 := b6e549682 X0
             grind)
          | exact resolve b6e549682 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e549682
        have b6e549725 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b6e549707 X0
             grind)
          | (have r₁ := b6e549707 X0
             have r₂ := b6e21
             grind)
          | exact resolve b6e549707 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e549707
        have b6e549879 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ x = (M.op (τ X0) x) := by
          intro X0
          first
          | (have i₁ := b6e27 X0 x
             have i₂ := b6e549725 (τ X0)
             grind)
          | exact superpose b6e549725 b6e27
          | (have j1 := b6e549725 (τ X0)
             grind)
          | exact resolve b6e27 b6e549725
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27 b6e549725
        have b6e550075 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op (τ X0) x) := by
          intro X0
          first
          | (have i₁ := b6e549879 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e549879
          | (have j0 := b6e549879 X0
             grind)
          | exact resolve b6e549879 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e549879
        have b6e551029 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (k x (τ X0)) ∨ x = (M.op (τ X0) x) := by
          intro X0
          first
          | (have i₁ := b6e5452 x X0
             have i₂ := b6e550075 X0
             grind)
          | exact superpose b6e550075 b6e5452
          | (have j0 := b6e5452 x X0
             have j1 := b6e550075 X0
             grind)
          | exact resolve b6e5452 b6e550075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5452 b6e550075
        have b6e551285 : ∀ X0 : G, x = (k x (τ X0)) ∨ (M.op (σ x) X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e551029 X0
             have j1 := b6e355599 (τ X0)
             grind)
          | (have r₁ := b6e551029 x
             have r₂ := b6e355599 (σ x)
             grind)
          | (have r₁ := b6e551029 X0
             have r₂ := b6e355599 (τ X0)
             grind)
          | exact resolve b6e551029 b6e355599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e355599 b6e551029
        have b6e553885 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e28 X0 x
             have i₂ := b6e551285 X0
             grind)
          | exact superpose b6e551285 b6e28
          | (have j1 := b6e551285 X0
             grind)
          | exact resolve b6e28 b6e551285
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e551285
        have b6e556813 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (k X0 (σ x)) = X0 ∨ (M.op (σ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e5127 (σ x) X0
             have i₂ := b6e553885 X0
             grind)
          | exact superpose b6e553885 b6e5127
          | (have j0 := b6e5127 (σ x) X0
             have j1 := b6e553885 X0
             grind)
          | exact resolve b6e5127 b6e553885
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5127 b6e553885
        have b6e556900 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b6e556813 X0
             have j1 := b6e18972 X0
             grind)
          | (have r₁ := b6e556813 (σ x)
             have r₂ := b6e18972 (σ x)
             grind)
          | (have r₁ := b6e556813 X0
             have r₂ := b6e18972 X0
             grind)
          | exact resolve b6e556813 b6e18972
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e18972 b6e556813
        have b6e560231 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e122 X0 (σ x)
             have i₂ := b6e556900 (σ X0)
             grind)
          | exact superpose b6e556900 b6e122
          | (have j1 := b6e556900 (σ X0)
             grind)
          | exact resolve b6e122 b6e556900
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e122 b6e556900
        have b6e560429 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e560231 X0
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e560231
          | (have j0 := b6e560231 X0
             grind)
          | exact resolve b6e560231 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e560231
        have b6e560461 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ x)) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b6e560429 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e560429
          | (have j0 := b6e560429 X0
             grind)
          | exact resolve b6e560429 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e560429
        have b6e569544 : ∀ X0 : G, (σ x) = (σ (k y X0)) ∨ (k X0 x) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b6e503788 X0
             have i₂ := b6e560461 X0
             grind)
          | exact superpose b6e560461 b6e503788
          | (have j0 := b6e503788 X0
             have j1 := b6e560461 X0
             grind)
          | exact resolve b6e503788 b6e560461
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e503788 b6e560461
        have b6e569755 : ∀ X0 : G, (σ x) = (σ (k y X0)) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b6e569544 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e569544
        have b6e570050 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 y) = (k (M.op X0 y) x) := by
          intro X0
          first
          | (have i₁ := b6e390941 X0
             have i₂ := b6e569755 (M.op X0 y)
             grind)
          | exact superpose b6e569755 b6e390941
          | (have j1 := b6e569755 (M.op X0 y)
             grind)
          | exact resolve b6e390941 b6e569755
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e390941
        have b6e570258 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) x) := by
          intro X0
          first
          | (have j0 := b6e570050 X0
             grind)
          | (have r₁ := b6e570050 X0
             have r₂ := b6e111
             grind)
          | exact resolve b6e570050 b6e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e570050
        have b6e570391 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op X0 y)) ∨ x = (M.op x (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e513282 (M.op X0 y)
             have i₂ := b6e570258 X0
             grind)
          | exact superpose b6e570258 b6e513282
          | (have j0 := b6e513282 (M.op X0 y)
             grind)
          | exact resolve b6e513282 b6e570258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e570258
        have b6e570424 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e570391 X0
             have i₂ := b6e39 y x X0
             grind)
          | exact superpose b6e39 b6e570391
          | (have j0 := b6e570391 X0
             grind)
          | exact resolve b6e570391 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e570391
        have b6e570439 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e570424 X0
             have i₂ := b6e71
             grind)
          | exact superpose b6e71 b6e570424
          | (have j0 := b6e570424 X0
             grind)
          | exact resolve b6e570424 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71 b6e570424
        have b6e570450 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e570439 X0
             have i₂ := b6e39 y x X0
             grind)
          | exact superpose b6e39 b6e570439
          | (have j0 := b6e570439 X0
             grind)
          | exact resolve b6e570439 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e570439
        have b6e570452 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b6e570450 X0
             grind)
          | (have r₁ := b6e570450 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e570450 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e570450
        have b6e570776 : ∀ X0 : G, y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b6e355601 X0 y
             have i₂ := b6e570452 X0
             grind)
          | exact superpose b6e570452 b6e355601
          | exact resolve b6e355601 b6e570452
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e355601
        have b6e571098 : ∀ X0 : G, y = (k x X0) ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b6e542166 X0
             have i₂ := b6e570776 X0
             grind)
          | exact superpose b6e570776 b6e542166
          | (have j0 := b6e542166 X0
             grind)
          | exact resolve b6e542166 b6e570776
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e542166
        have b6e571103 : ∀ X0 : G, (σ x) = (σ y) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b6e569755 X0
             have i₂ := b6e570776 X0
             grind)
          | exact superpose b6e570776 b6e569755
          | (have j0 := b6e569755 X0
             grind)
          | exact resolve b6e569755 b6e570776
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e569755 b6e570776
        have b6e571484 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b6e571103 X0
             grind)
          | (have r₁ := b6e571103 X0
             have r₂ := b6e111
             grind)
          | exact resolve b6e571103 b6e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e571103
        have b6e571558 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e513282 X0
             have i₂ := b6e571484 X0
             grind)
          | exact superpose b6e571484 b6e513282
          | (have j0 := b6e513282 X0
             grind)
          | exact resolve b6e513282 b6e571484
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e513282 b6e571484
        have b6e580269 : ∀ X0 : G, (τ (M.op X0 x)) = (τ y) ∨ (M.op X0 x) = X0 ∨ x = (M.op x X0) ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b6e15242 X0 x
             have i₂ := b6e571098 X0
             grind)
          | exact superpose b6e571098 b6e15242
          | (have j0 := b6e15242 X0 x
             have j1 := b6e571098 X0
             grind)
          | exact resolve b6e15242 b6e571098
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e571098
        have b6e580534 : ∀ X0 : G, (τ (M.op X0 x)) = (τ y) ∨ x = (M.op x X0) ∨ x = (k x X0) := by
          intro X0
          first
          | (have j0 := b6e580269 X0
             have j1 := b6e16 x X0
             grind)
          | (have r₁ := b6e580269 x
             have r₂ := b6e16 x x
             grind)
          | (have r₁ := b6e580269 X0
             have r₂ := b6e16 X0 x
             grind)
          | exact resolve b6e580269 b6e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e580269
        have b6e580557 : ∀ X0 : G, (τ (M.op X0 x)) = (τ y) ∨ x = (k x X0) := by
          intro X0
          first
          | (have j0 := b6e580534 X0
             have j1 := b6e15 x X0
             grind)
          | (have r₁ := b6e580534 x
             have r₂ := b6e15 x x
             grind)
          | exact resolve b6e580534 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e580534
        have b6e580637 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op x X0) ∨ x = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e571558 (M.op x X1)
             have i₂ := b6e39 X1 x x
             grind)
          | exact superpose b6e39 b6e571558
          | (have j0 := b6e571558 X0
             grind)
          | exact resolve b6e571558 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e580917 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 x) ∨ (M.op x X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e39 X1 X0 x
             have i₂ := b6e571558 X1
             grind)
          | exact superpose b6e571558 b6e39
          | (have j1 := b6e571558 X1
             grind)
          | exact resolve b6e39 b6e571558
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e589696 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = x ∨ x = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e571558 X0
             have i₂ := b6e580637 X0 x
             grind)
          | (have i₁ := b6e571558 X0
             have i₂ := b6e580637 X0 X1
             grind)
          | exact superpose b6e580637 b6e571558
          | (have j0 := b6e571558 X1
             have j1 := b6e580637 X1 X1
             grind)
          | exact resolve b6e571558 b6e580637
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e571558
        have b6e589987 : ∀ X0 X1 : G, (M.op X1 X0) ≠ x ∨ x = (M.op x X0) := by
          intro X0 X1
          first
          | (have j0 := b6e580637 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e580637
        have b6e590027 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ x = (M.op x X1) := by
          intro X0 X1
          first
          | (have j0 := b6e589696 X0 X1
             have j1 := b6e589987 X1 X1
             grind)
          | (have r₁ := b6e589696 X1 x
             have r₂ := b6e589987 x X1
             grind)
          | (have r₁ := b6e589696 X1 X0
             have r₂ := b6e589987 X0 X1
             grind)
          | (have r₁ := b6e589696 X0 X0
             have r₂ := b6e589987 X0 x
             grind)
          | exact resolve b6e589696 b6e589987
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e589696 b6e589987
        have b6e591240 : (σ x) = (σ y) ∨ x = (M.op x (σ x)) := by
          first
          | (have i₁ := b6e390316
             have i₂ := b6e590027 (σ y) (σ x)
             grind)
          | exact superpose b6e590027 b6e390316
          | (have j1 := b6e590027 x (σ x)
             grind)
          | exact resolve b6e390316 b6e590027
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e591386 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 x) ∨ (M.op X2 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e39 X1 X0 x
             have i₂ := b6e590027 X2 X1
             grind)
          | exact superpose b6e590027 b6e39
          | (have j1 := b6e590027 X2 X1
             grind)
          | exact resolve b6e39 b6e590027
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e590027
        have b6e591753 : x = (M.op x (σ x)) := by
          first
          | (have r₁ := b6e591240
             have r₂ := b6e111
             grind)
          | exact resolve b6e591240 b6e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e591240
        have b6e592019 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e39 (σ x) X0 x
             have i₂ := b6e591753
             grind)
          | exact superpose b6e591753 b6e39
          | exact resolve b6e39 b6e591753
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39 b6e591753
        have b6e592261 : ∀ X0 : G, x = (k x (τ (M.op X0 x))) := by
          intro X0
          first
          | (have i₁ := b6e756 X0
             have i₂ := b6e592019 X0
             grind)
          | exact superpose b6e592019 b6e756
          | exact resolve b6e756 b6e592019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e756
        have b6e592561 : (σ y) = (M.op (σ y) x) := by
          first
          | (have i₁ := b6e390316
             have i₂ := b6e592019 (σ y)
             grind)
          | exact superpose b6e592019 b6e390316
          | exact resolve b6e390316 b6e592019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e390316
        have b6e593534 : ∀ X0 : G, x = (k x (τ y)) ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b6e592261 X0
             have i₂ := b6e580557 X0
             grind)
          | exact superpose b6e580557 b6e592261
          | (have j1 := b6e580557 (τ y)
             grind)
          | exact resolve b6e592261 b6e580557
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e580557 b6e592261
        have b6e604919 : x ≠ x ∨ x = (k x (τ y)) := by
          first
          | (have j0 := b6e593534 (τ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e593534
        have b6e604920 : x = (k x (τ y)) := by grind
        clear b6e604919
        have b6e605050 : (σ x) = (k (σ x) y) := by
          first
          | (have i₁ := b6e28 y x
             have i₂ := b6e604920
             grind)
          | exact superpose b6e604920 b6e28
          | exact resolve b6e28 b6e604920
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e604920
        have b6e605218 : y ≠ (σ x) ∨ y = (M.op y (σ x)) := by
          first
          | (have i₁ := b6e545233 (σ x)
             have i₂ := b6e605050
             grind)
          | exact superpose b6e605050 b6e545233
          | (have j0 := b6e545233 (σ x)
             grind)
          | exact resolve b6e545233 b6e605050
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e545233
        have b6e605219 : (σ x) = (M.op y (σ x)) ∨ y = (M.op y (σ x)) := by
          first
          | (have i₁ := b6e548977 (σ x)
             have i₂ := b6e605050
             grind)
          | exact superpose b6e605050 b6e548977
          | (have j0 := b6e548977 (σ x)
             grind)
          | exact resolve b6e548977 b6e605050
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e548977
        have b6e605235 : (τ (σ x)) = (τ (M.op y (σ x))) ∨ y = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e15242 y (σ x)
             have i₂ := b6e605050
             grind)
          | exact superpose b6e605050 b6e15242
          | (have j0 := b6e15242 y (σ x)
             grind)
          | exact resolve b6e15242 b6e605050
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15242 b6e605050
        have b6e605266 : (τ (σ x)) = (τ (M.op y x)) ∨ y = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e605235
             have i₂ := b6e592019 y
             grind)
          | exact superpose b6e592019 b6e605235
          | exact resolve b6e605235 b6e592019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605235
        have b6e605270 : (σ x) = (M.op y x) ∨ y = (M.op y (σ x)) := by
          first
          | (have i₁ := b6e605219
             have i₂ := b6e592019 y
             grind)
          | exact superpose b6e592019 b6e605219
          | exact resolve b6e605219 b6e592019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605219
        have b6e605271 : y = (M.op y x) ∨ y ≠ (σ x) := by
          first
          | (have i₁ := b6e605218
             have i₂ := b6e592019 y
             grind)
          | exact superpose b6e592019 b6e605218
          | exact resolve b6e605218 b6e592019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605218
        have b6e605318 : (τ (σ x)) = (τ x) ∨ y = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e605266
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e605266
          | exact resolve b6e605266 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605266
        have b6e605322 : x = (σ x) ∨ y = (M.op y (σ x)) := by
          first
          | (have i₁ := b6e605270
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e605270
          | exact resolve b6e605270 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65 b6e605270
        have b6e605323 : y ≠ (σ x) := by
          first
          | (have r₁ := b6e605271
             have r₂ := b6e21
             grind)
          | exact resolve b6e605271 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605271
        have b6e605361 : x = (τ x) ∨ y = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e605318
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e605318
          | exact resolve b6e605318 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605318
        have b6e605364 : y = (M.op y x) ∨ x = (σ x) := by
          first
          | (have i₁ := b6e605322
             have i₂ := b6e592019 y
             grind)
          | exact superpose b6e592019 b6e605322
          | exact resolve b6e605322 b6e592019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605322
        have b6e605383 : y = (M.op y x) ∨ x = (τ x) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e605361
             have i₂ := b6e592019 y
             grind)
          | exact superpose b6e592019 b6e605361
          | exact resolve b6e605361 b6e592019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605361
        have b6e605386 : x = (σ x) := by
          first
          | (have r₁ := b6e605364
             have r₂ := b6e21
             grind)
          | exact resolve b6e605364 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605364
        have b6e605402 : x = (τ x) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have r₁ := b6e605383
             have r₂ := b6e21
             grind)
          | exact resolve b6e605383 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605383
        have b6e605413 : y = (σ x) ∨ x = (τ x) := by
          first
          | (have i₁ := b6e605402
             have i₂ := b6e570452 (σ x)
             grind)
          | exact superpose b6e570452 b6e605402
          | exact resolve b6e605402 b6e570452
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605402
        have b6e605415 : x = (τ x) := by
          first
          | (have r₁ := b6e605413
             have r₂ := b6e605323
             grind)
          | exact resolve b6e605413 b6e605323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605413
        have b6e619442 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X2 X0) = (M.op X2 x) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e351453 X0 X1 x
             have i₂ := b6e580917 X0 X1
             grind)
          | exact superpose b6e580917 b6e351453
          | (have j1 := b6e580917 X2 X0
             grind)
          | (have r₁ := b6e351453 X0 x X0
             have r₂ := b6e580917 X0 x
             grind)
          | exact resolve b6e351453 b6e580917
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e351453 b6e580917
        have b6e619666 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X2 X0) = (M.op X2 x) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e619442 X0 X1 X2
             have j1 := b6e591386 X2 X0 X2
             grind)
          | (have r₁ := b6e619442 (M.op X0 x) X0 X2
             have r₂ := b6e591386 X0 (M.op X0 x) X2
             grind)
          | (have r₁ := b6e619442 X1 X2 X2
             have r₂ := b6e591386 X0 X1 X2
             grind)
          | exact resolve b6e619442 b6e591386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e591386 b6e619442
        have b6e629285 : ∀ X0 X1 : G, (σ y) ≠ (M.op (σ y) x) ∨ (k X0 (σ y)) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e392753 X0
             have i₂ := b6e619666 X0 X1 (σ y)
             grind)
          | (have i₁ := b6e392753 x
             have i₂ := b6e619666 X0 X1 (σ y)
             grind)
          | exact superpose b6e619666 b6e392753
          | (have j0 := b6e392753 x
             have j1 := b6e619666 X0 (σ y) x
             grind)
          | exact resolve b6e392753 b6e619666
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e392753 b6e619666
        have b6e629650 : ∀ X0 X1 : G, (k X0 (σ y)) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e629285 X0 (σ y)
             grind)
          | (have r₁ := b6e629285 X0 X1
             have r₂ := b6e592561
             grind)
          | exact resolve b6e629285 b6e592561
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e592561 b6e629285
        have b6e630466 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e629650 X0 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e629650
        have b6e630467 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e630466 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e630466
        have b6e630716 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e630467 (σ X0)
             grind)
          | exact superpose b6e630467 b6e18
          | exact resolve b6e18 b6e630467
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e630467
        have b6e632582 : (σ (σ y)) = (σ (M.op y (σ x))) ∨ y = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e630716 (σ y)
             have i₂ := b6e17745 y
             grind)
          | exact superpose b6e17745 b6e630716
          | (have j1 := b6e17745 y
             grind)
          | exact resolve b6e630716 b6e17745
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17745 b6e630716
        have b6e633027 : (σ (M.op y x)) = (σ (σ y)) ∨ y = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e632582
             have i₂ := b6e592019 y
             grind)
          | exact superpose b6e592019 b6e632582
          | exact resolve b6e632582 b6e592019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e632582
        have b6e633072 : (σ x) = (σ (σ y)) ∨ y = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e633027
             have i₂ := b6e64
             grind)
          | exact superpose b6e64 b6e633027
          | exact resolve b6e633027 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64 b6e633027
        have b6e633086 : x = (σ (σ y)) ∨ y = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e633072
             have i₂ := b6e605386
             grind)
          | exact superpose b6e605386 b6e633072
          | exact resolve b6e633072 b6e605386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e633072
        have b6e633090 : y = (M.op y x) ∨ x = (σ (σ y)) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e633086
             have i₂ := b6e592019 y
             grind)
          | exact superpose b6e592019 b6e633086
          | exact resolve b6e633086 b6e592019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e592019 b6e633086
        have b6e633092 : x = (σ (σ y)) ∨ (σ x) = (M.op (σ x) y) := by
          first
          | (have r₁ := b6e633090
             have r₂ := b6e21
             grind)
          | exact resolve b6e633090 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e633090
        have b6e633094 : y = (σ x) ∨ x = (σ (σ y)) := by
          first
          | (have i₁ := b6e633092
             have i₂ := b6e570452 (σ x)
             grind)
          | exact superpose b6e570452 b6e633092
          | exact resolve b6e633092 b6e570452
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e570452 b6e633092
        have b6e633096 : x = (σ (σ y)) := by
          first
          | (have r₁ := b6e633094
             have r₂ := b6e605323
             grind)
          | exact resolve b6e633094 b6e605323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605323 b6e633094
        have b6e633129 : (σ y) = (τ x) := by
          first
          | (have i₁ := b6e13 (σ y)
             have i₂ := b6e633096
             grind)
          | exact superpose b6e633096 b6e13
          | exact resolve b6e13 b6e633096
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e633096
        have b6e633450 : x = (σ y) := by
          first
          | (have i₁ := b6e633129
             have i₂ := b6e605415
             grind)
          | exact superpose b6e605415 b6e633129
          | exact resolve b6e633129 b6e605415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e605415 b6e633129
        have b6e633532 : x ≠ (σ x) := by
          first
          | (have i₁ := b6e111
             have i₂ := b6e633450
             grind)
          | exact superpose b6e633450 b6e111
          | exact resolve b6e111 b6e633450
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e111 b6e633450
        have b6e634026 : False := by grind
        exact b6e634026
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
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
          have b7e26 : (σ y) = (k (σ y) (σ x)) := by grind
          clear b7e25
          have b7e27 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e26
            | exact resolve b7e26 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b7e32 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e27
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : y = (k y x) := by
            first
            | (have i₁ := b7e32
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e32
            | exact resolve b7e32 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e36 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 X1)) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op X0 X0) X1 X2
               have i₂ := b7e13 X0 X0 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op X3 X1) (M.op X0 X0)
               have i₂ := b7e13 X0 X1 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e16 (M.op X0 X0) (M.op X2 X1)
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e16
            | (have j0 := b7e16 (M.op X0 X0) (M.op X2 X1)
               grind)
            | (have r₁ := b7e16 (M.op X1 X1) (M.op X2 X1)
               have r₂ := b7e13 X1 X1 X2
               grind)
            | exact resolve b7e16 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
            intro X1 X2 X3
            first
            | (have i₁ := b7e38 x X1 X2 X3
               have i₂ := b7e13 X2 X1 x
               grind)
            | exact superpose b7e13 b7e38
            | exact resolve b7e38 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e41 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e36 X0 X1 x
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e36
            | exact resolve b7e36 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e42 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e40 (σ x) X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e40
            | exact resolve b7e40 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e54 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e57 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e54
          have b7e60 : (σ x) = (k (σ x) (σ y)) := by
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
          have b7e64 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e61
               grind)
            | exact superpose b7e61 b7e14
            | exact resolve b7e14 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e65 : x = (k x y) := by
            first
            | (have i₁ := b7e64
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e64
            | exact resolve b7e64 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e70 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 X0
               have i₂ := b7e18 (σ X1) (σ X0)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X0) (σ X1)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e72 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e33
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e33 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e73 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e27
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e27
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e27 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e74 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e73
               have r₂ := b7e21
               grind)
            | exact resolve b7e73 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e75 : y = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e72
               have r₂ := b7e21
               grind)
            | exact resolve b7e72 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e78 : (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e22
               grind)
            | exact resolve b7e74 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e79 : y = (M.op x y) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e22
               grind)
            | exact resolve b7e75 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e83 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e84 : x = (M.op y x) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e83
               have r₂ := b7e22
               grind)
            | exact resolve b7e83 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e86 : x = (M.op y x) := by
            first
            | (have r₁ := b7e84
               have r₂ := b7e21
               grind)
            | exact resolve b7e84 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e152 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e39 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e200 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e42 (σ x)
               grind)
            | exact superpose b7e42 b7e20
            | exact resolve b7e20 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e201 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e42 (σ x)
               grind)
            | exact superpose b7e42 b7e23
            | exact resolve b7e23 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e202 : (σ y) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e200
               have i₂ := b7e78
               grind)
            | exact superpose b7e78 b7e200
            | exact resolve b7e200 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78 b7e200
          have b7e264 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (σ X1) (σ X0)
               have i₂ := b7e70 X1 X0
               grind)
            | exact superpose b7e70 b7e17
            | (have j0 := b7e17 (σ X1) (σ X0)
               have j1 := b7e70 X1 X0
               grind)
            | (have r₁ := b7e17 (σ X0) (σ X1)
               have r₂ := b7e70 X0 X1
               grind)
            | (have r₁ := b7e17 (σ X1) (σ X0)
               have r₂ := b7e70 X0 X1
               grind)
            | exact resolve b7e17 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e269 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e70 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e272 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e264 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e264
          have b7e273 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e272 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e272
          have b7e283 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e273 X0 X1
               have j1 := b7e16 (σ X1) (σ X0)
               grind)
            | (have r₁ := b7e273 X0 X1
               have r₂ := b7e16 (σ X1) (σ X0)
               grind)
            | exact resolve b7e273 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e273
          have b7e310 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e283 X0 X1
               have i₂ := b7e19 X1 X0
               grind)
            | exact superpose b7e19 b7e283
            | (have j0 := b7e283 X0 X1
               grind)
            | exact resolve b7e283 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e283
          have b7e342 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e202
               have i₂ := b7e70 x x
               grind)
            | exact superpose b7e70 b7e202
            | (have j1 := b7e70 x x
               grind)
            | exact resolve b7e202 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e202
          have b7e343 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b7e342
          have b7e344 : (σ y) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b7e343
               have r₂ := b7e201
               grind)
            | exact resolve b7e343 b7e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e343
          have b7e378 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e152 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e152
            | exact resolve b7e152 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e152
          have b7e1015 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e310 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e310
            | exact resolve b7e310 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e310
          have b7e1090 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e1015 X0 X1
               have i₂ := b7e29 X0 X1
               grind)
            | exact superpose b7e29 b7e1015
            | (have j0 := b7e1015 X0 X1
               grind)
            | exact resolve b7e1015 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29 b7e1015
          have b7e1102 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e1090 X0 X1
               have i₂ := b7e28 X0 X1
               grind)
            | exact superpose b7e28 b7e1090
            | (have j0 := b7e1090 X0 X1
               grind)
            | exact resolve b7e1090 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e1090
          have b7e3888 : (σ (k x x)) = (k (σ (k x x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e378
               have i₂ := b7e70 x x
               grind)
            | exact superpose b7e70 b7e378
            | (have j1 := b7e70 x x
               grind)
            | exact resolve b7e378 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e378
          have b7e3901 : (σ (k x x)) = (k (σ (k x x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b7e3888
          have b7e3904 : (σ (k x x)) = (k (σ (k x x)) (σ y)) := by
            first
            | (have r₁ := b7e3901
               have r₂ := b7e201
               grind)
            | exact resolve b7e3901 b7e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3901
          have b7e3907 : (σ (k x x)) = (σ (k (k x x) y)) := by
            first
            | (have i₁ := b7e3904
               have i₂ := b7e19 (k x x) y
               grind)
            | exact superpose b7e19 b7e3904
            | exact resolve b7e3904 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3904
          have b7e3916 : (k (k x x) y) = (τ (σ (k x x))) := by
            first
            | (have i₁ := b7e14 (k (k x x) y)
               have i₂ := b7e3907
               grind)
            | exact superpose b7e3907 b7e14
            | exact resolve b7e14 b7e3907
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3907
          have b7e3962 : (k x x) = (k (k x x) y) := by
            first
            | (have i₁ := b7e3916
               have i₂ := b7e14 (k x x)
               grind)
            | exact superpose b7e14 b7e3916
            | exact resolve b7e3916 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3916
          have b7e3997 : (M.op x x) = (k (M.op x x) y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e3962
               have i₂ := b7e18 x x
               grind)
            | exact superpose b7e18 b7e3962
            | (have j1 := b7e18 x x
               grind)
            | exact resolve b7e3962 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3962
          have b7e4005 : (M.op x x) = (k (M.op x x) y) ∨ x = (M.op x x) := by grind
          clear b7e3997
          have b7e5002 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e1102 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e1102
            | exact resolve b7e1102 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1102
          have b7e5263 : (σ y) ≠ (σ (M.op x x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b7e344
               have i₂ := b7e5002 x x
               grind)
            | exact superpose b7e5002 b7e344
            | (have j1 := b7e5002 x x
               grind)
            | exact resolve b7e344 b7e5002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e344 b7e5002
          have b7e9702 : (M.op x x) = (M.op y (M.op x x)) ∨ y = (M.op y (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 (M.op x x) y
               have i₂ := b7e4005
               grind)
            | exact superpose b7e4005 b7e18
            | (have j0 := b7e18 (M.op x x) y
               grind)
            | exact resolve b7e18 b7e4005
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4005
          have b7e9716 : (M.op y x) = (M.op x x) ∨ y = (M.op y (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e9702
               have i₂ := b7e40 x y x
               grind)
            | exact superpose b7e40 b7e9702
            | exact resolve b7e9702 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9702
          have b7e9724 : x = (M.op x x) ∨ y = (M.op y (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e9716
               have i₂ := b7e86
               grind)
            | exact superpose b7e86 b7e9716
            | exact resolve b7e9716 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86 b7e9716
          have b7e9725 : x = (M.op x x) ∨ y = (M.op y (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) y) := by grind
          clear b7e9724
          have b7e9731 : y = (M.op y x) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b7e9725
               have i₂ := b7e40 x y x
               grind)
            | exact superpose b7e40 b7e9725
            | exact resolve b7e9725 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e9725
          have b7e9734 : x = (M.op x x) ∨ (M.op x x) = (M.op (M.op x x) y) := by
            first
            | (have r₁ := b7e9731
               have r₂ := b7e22
               grind)
            | exact resolve b7e9731 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9731
          have b7e9737 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e9734
               have i₂ := b7e41 x y
               grind)
            | exact superpose b7e41 b7e9734
            | exact resolve b7e9734 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41 b7e9734
          have b7e9740 : y = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e9737
               have i₂ := b7e79
               grind)
            | exact superpose b7e79 b7e9737
            | exact resolve b7e9737 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e9737
          have b7e10010 : (σ y) ≠ (σ y) ∨ x = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e5263
               have i₂ := b7e9740
               grind)
            | exact superpose b7e9740 b7e5263
            | exact resolve b7e5263 b7e9740
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5263 b7e9740
          have b7e10051 : x = (k x x) ∨ x = (M.op x x) := by grind
          clear b7e10010
          have b7e10068 : x = (k x x) := by
            first
            | (have j1 := b7e16 x x
               grind)
            | (have r₁ := b7e10051
               have r₂ := b7e16 x x
               grind)
            | exact resolve b7e10051 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10051
          have b7e10391 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e269 x x
               have i₂ := b7e10068
               grind)
            | exact superpose b7e10068 b7e269
            | (have j0 := b7e269 x x
               grind)
            | exact resolve b7e269 b7e10068
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e269 b7e10068
          have b7e10394 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b7e10391
          have b7e10395 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b7e10394
          have b7e10400 : False := by grind
          exact b7e10400
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e168 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e63 x y
               grind)
            | exact superpose b8e63 b8e24
            | (have j1 := b8e63 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e63 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e63 y x
               grind)
            | exact resolve b8e24 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e181 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e168
          have b8e191 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e181
               have r₂ := b8e23
               grind)
            | exact resolve b8e181 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e181
          have b8e202 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e191
               grind)
            | exact superpose b8e191 b8e20
            | exact resolve b8e20 b8e191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e191
          have b8e264 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e202
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e202
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e202 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e202
          have b8e265 : x = (M.op x y) ∨ y = (M.op y x) := by grind
          clear b8e264
          have b8e266 : y = (M.op y x) := by
            first
            | (have r₁ := b8e265
               have r₂ := b8e21
               grind)
            | exact resolve b8e265 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e265
          have b8e267 : False := by grind
          exact b8e267

/-- `Equation4441`: `x ◇ (y ◇ x) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pxy_Equation4441 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4441 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4441.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
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
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
      have b0e35 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) (σ x) X0 X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) X0 (σ x) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X0 x X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 x x
           have i₂ := b0e11 X0 X2 x x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e41 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e41
        | exact resolve b0e41 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op x X2) X3) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e11 x x X2 X3
           have i₂ := b0e41 x X0
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (M.op X3 X3) ∨ (k X3 (M.op X0 X2)) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e15 X3 (M.op X0 X2)
           have i₂ := b0e11 X0 X1 X2 X3
           grind)
        | exact superpose b0e11 b0e15
        | (have j0 := b0e15 X3 (M.op X0 X2)
           grind)
        | (have r₁ := b0e15 X3 (M.op X0 (M.op X1 X0))
           have r₂ := b0e11 X0 X1 (M.op X1 X0) X3
           grind)
        | exact resolve b0e15 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e67 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e41 X0 x
           have i₂ := b0e46 x
           grind)
        | exact superpose b0e46 b0e41
        | exact resolve b0e41 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op x y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 y X1 X2
           have i₂ := b0e46 X0
           grind)
        | exact superpose b0e46 b0e11
        | exact resolve b0e11 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e73 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e41 y X0
           have i₂ := b0e46 x
           grind)
        | exact superpose b0e46 b0e41
        | exact resolve b0e41 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e74 : (M.op x y) = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b0e73 x
           have i₂ := b0e46 x
           grind)
        | exact superpose b0e46 b0e73
        | exact resolve b0e73 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73
      have b0e83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b0e88 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op X1 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X2 X1 X3
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2 X3
           have i₂ := b0e16 X0 (M.op X0 X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X1 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e89 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X2) X3) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X1 X2 X3
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2 X3
           have i₂ := b0e16 X0 (M.op X1 X0)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X1 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e90 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = X0 ∨ (k (M.op X1 X3) X0) = (M.op (M.op X1 X3) X0) ∨ (M.op X0 (M.op X1 X3)) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X2 X3 (M.op X1 X3)
           have i₂ := b0e16 (M.op X1 X3) X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2 X3
           have i₂ := b0e16 X0 (M.op (M.op X0 X2) X3)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 (M.op X1 X3) X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e92 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 X3) X0) = (M.op X1 (M.op x y)) ∨ (M.op X1 (M.op X2 X1)) = X0 ∨ (M.op X0 (M.op X1 X3)) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e90 X0 X1 X2 X3
           have i₂ := b0e71 X1 X3 X0
           grind)
        | exact superpose b0e71 b0e90
        | (have j0 := b0e90 X0 X1 X2 X3
           grind)
        | exact resolve b0e90 b0e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90
      have b0e93 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op x y)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e89 X0 X1 x x
           have i₂ := b0e71 X1 x x
           grind)
        | exact superpose b0e71 b0e89
        | (have j0 := b0e89 X0 X1 x x
           grind)
        | exact resolve b0e89 b0e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89
      have b0e141 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e290 : ∀ X0 X1 : G, (M.op x X1) = (k (M.op x X1) (M.op y X0)) := by
        intro X0 X1
        grind
      clear b0e51
      have b0e305 : ∀ X1 : G, (M.op x X1) = (k (M.op x X1) (M.op x y)) := by
        intro X1
        first
        | (have i₁ := b0e290 x X1
           have i₂ := b0e46 x
           grind)
        | exact superpose b0e46 b0e290
        | exact resolve b0e290 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e290
      have b0e384 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op x y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e42 X0 X1 y
           have i₂ := b0e46 X0
           grind)
        | exact superpose b0e46 b0e42
        | exact resolve b0e42 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e481 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e35 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e35
        | exact resolve b0e35 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e1933 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e481 X0
           grind)
        | exact superpose b0e481 b0e18
        | exact resolve b0e18 b0e481
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2595 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X2) = (k X4 X2) ∨ (M.op X4 X0) = (k X4 X0) ∨ (M.op X0 X1) = (M.op X2 X3) ∨ (M.op X2 X4) = X2 ∨ (M.op X0 X4) = X0 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e88 X0 X4 x X1
           have i₂ := b0e88 X2 X4 x X3
           grind)
        | (have i₁ := b0e88 X0 X0 X2 X3
           have i₂ := b0e88 X0 X1 X2 (M.op X2 X0)
           grind)
        | exact superpose b0e88 b0e88
        | (have j0 := b0e88 X2 X4 X2 X3
           have j1 := b0e88 X2 X4 X2 X3
           grind)
        | exact resolve b0e88 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2767 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e88 X0 X1 X2 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e3085 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 (M.op x y)) = X1 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e16 X0 X1
           have i₂ := b0e93 X0 X0
           grind)
        | (have i₁ := b0e16 (M.op x y) X1
           have i₂ := b0e93 X0 (M.op x y)
           grind)
        | exact superpose b0e93 b0e16
        | (have j0 := b0e16 X0 X0
           have j1 := b0e93 X1 X0
           grind)
        | exact resolve b0e16 b0e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93
      have b0e3358 : ∀ X0 X1 X3 : G, (M.op (σ y) X0) ≠ (M.op (σ x) (M.op X1 (σ x))) ∨ (M.op X3 X3) = (M.op (σ y) X0) ∨ (k X3 (M.op (σ y) X0)) = X3 := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e59 (σ x) X1 (M.op X0 (σ x)) X3
           have i₂ := b0e40 X0 X1
           grind)
        | exact superpose b0e40 b0e59
        | (have j0 := b0e59 (σ y) X1 X0 X3
           grind)
        | exact resolve b0e59 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e3376 : ∀ X0 X3 : G, (M.op X3 X3) = (M.op (σ y) X0) ∨ (k X3 (M.op (σ y) X0)) = X3 := by
        intro X0 X3
        first
        | (have j0 := b0e3358 X0 x X3
           grind)
        | (have r₁ := b0e3358 x X0 X3
           have r₂ := b0e40 X0 x
           grind)
        | exact resolve b0e3358 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e3358
      have b0e3777 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (k y X0) ∨ (M.op x (M.op X1 x)) = X0 ∨ (M.op X0 y) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e92 X0 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e92
        | (have j0 := b0e92 X0 x X1 x
           grind)
        | exact resolve b0e92 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92
      have b0e4061 : ∀ X0 X1 : G, (M.op x y) = (k y X0) ∨ (M.op x (M.op X1 x)) = X0 ∨ (M.op X0 y) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e3777 X0 X1
           have i₂ := b0e74
           grind)
        | exact superpose b0e74 b0e3777
        | (have j0 := b0e3777 X0 X1
           grind)
        | exact resolve b0e3777 b0e74
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74 b0e3777
      have b0e4157 : ∀ X0 : G, (M.op x y) = (k y X0) ∨ (M.op x y) = X0 ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e4061 X0 x
           have i₂ := b0e67 x
           grind)
        | exact superpose b0e67 b0e4061
        | (have j0 := b0e4061 X0 x
           grind)
        | exact resolve b0e4061 b0e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67 b0e4061
      have b0e4903 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e83 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83
      have b0e4904 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e4903 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4903
      have b0e17882 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e4904 (M.op x y)
           have i₂ := b0e305 y
           grind)
        | exact superpose b0e305 b0e4904
        | (have j0 := b0e4904 (M.op x y)
           grind)
        | exact resolve b0e4904 b0e305
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e305 b0e4904
      have b0e17895 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
      clear b0e17882
      have b0e18104 : ∀ X0 X1 : G, (k X1 (M.op (σ y) X0)) = X1 ∨ (k X1 (M.op (σ y) X0)) = X1 := by
        intro X0 X1
        grind
      clear b0e3376
      have b0e18340 : ∀ X0 X1 : G, (k X1 (M.op (σ y) X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e18104 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18104
      have b0e18593 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e18340 x X0
           have i₂ := b0e481 x
           grind)
        | exact superpose b0e481 b0e18340
        | exact resolve b0e18340 b0e481
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18340
      have b0e18810 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ x) (σ y)))) := by
        intro X0
        first
        | (have i₁ := b0e141 X0 (M.op (σ x) (σ y))
           have i₂ := b0e18593 (σ X0)
           grind)
        | exact superpose b0e18593 b0e141
        | exact resolve b0e141 b0e18593
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141 b0e18593
      have b0e18816 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e18810 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e18810
        | exact resolve b0e18810 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18810
      have b0e21084 : ∀ X1 : G, (M.op x y) ≠ X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
        intro X1
        first
        | (have i₁ := b0e2767 X1 y x
           have i₂ := b0e46 (M.op x y)
           grind)
        | exact superpose b0e46 b0e2767
        | (have j0 := b0e2767 X1 y x
           grind)
        | (have r₁ := b0e2767 (M.op x y) y x
           have r₂ := b0e46 (M.op x y)
           grind)
        | exact resolve b0e2767 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2767
      have b0e21088 : ∀ X1 : G, (M.op x y) = (k y X1) ∨ (M.op x y) ≠ X1 ∨ (M.op X1 y) = X1 := by
        intro X1
        first
        | (have i₁ := b0e21084 X1
           have i₂ := b0e46 X1
           grind)
        | exact superpose b0e46 b0e21084
        | (have j0 := b0e21084 X1
           grind)
        | (have r₁ := b0e21084 (M.op y x)
           have r₂ := b0e46 x
           grind)
        | exact resolve b0e21084 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21084
      have b0e21201 : ∀ X1 : G, (M.op x y) = (k y X1) ∨ (M.op X1 y) = X1 := by
        intro X1
        first
        | (have j0 := b0e21088 X1
           have j1 := b0e4157 X1
           grind)
        | (have r₁ := b0e21088 (k y x)
           have r₂ := b0e4157 x
           grind)
        | (have r₁ := b0e21088 x
           have r₂ := b0e4157 x
           grind)
        | (have r₁ := b0e21088 (M.op x y)
           have r₂ := b0e4157 (M.op x y)
           grind)
        | exact resolve b0e21088 b0e4157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4157 b0e21088
      have b0e32783 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) X0) ∨ (τ X0) = (M.op (τ X0) y) := by
        intro X0
        first
        | (have i₁ := b0e26 X0 y
           have i₂ := b0e21201 (τ X0)
           grind)
        | exact superpose b0e21201 b0e26
        | (have j1 := b0e21201 (τ X0)
           grind)
        | exact resolve b0e26 b0e21201
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e48146 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) := by
        first
        | (have i₁ := b0e384 (σ (M.op x y)) (σ (M.op x y))
           have i₂ := b0e17895
           grind)
        | exact superpose b0e17895 b0e384
        | exact resolve b0e384 b0e17895
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e384
      have b0e48235 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op x y)) := by
        first
        | (have i₁ := b0e48146
           have i₂ := b0e17895
           grind)
        | exact superpose b0e17895 b0e48146
        | exact resolve b0e48146 b0e17895
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e17895 b0e48146
      have b0e53502 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e71 (σ (M.op x y)) (M.op x y) x
           have i₂ := b0e48235
           grind)
        | exact superpose b0e48235 b0e71
        | exact resolve b0e71 b0e48235
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71 b0e48235
      have b0e109865 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e2595 X0 X1 X0 x X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2595
      have b0e109866 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e109865 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109865
      have b0e124732 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 (M.op x y)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e3085 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3085
      have b0e124733 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 (M.op x y)) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e124732 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e124732
      have b0e124734 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 (M.op x y)) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e124733 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e124733
      have b0e124992 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e124734 X0
           have j1 := b0e109866 X0 X0 x
           grind)
        | (have r₁ := b0e124734 X0
           have r₂ := b0e109866 X0 x (M.op x y)
           grind)
        | (have r₁ := b0e124734 x
           have r₂ := b0e109866 x x x
           grind)
        | exact resolve b0e124734 b0e109866
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109866 b0e124734
      have b0e179773 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) y) := by
        first
        | (have i₁ := b0e124992 (σ y)
           have i₂ := b0e32783 (σ y)
           grind)
        | exact superpose b0e32783 b0e124992
        | (have j0 := b0e124992 (σ y)
           have j1 := b0e32783 (σ y)
           grind)
        | exact resolve b0e124992 b0e32783
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32783 b0e124992
      have b0e180010 : (σ y) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) y) := by
        first
        | (have r₁ := b0e179773
           have r₂ := b0e1933 (σ y)
           grind)
        | exact resolve b0e179773 b0e1933
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179773
      have b0e180141 : (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) y) := by
        first
        | (have i₁ := b0e180010
           have i₂ := b0e481 (σ y)
           grind)
        | exact superpose b0e481 b0e180010
        | exact resolve b0e180010 b0e481
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e481 b0e180010
      have b0e180183 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e180141
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e180141
        | exact resolve b0e180141 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e180141
      have b0e180199 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e180183
           have i₂ := b0e46 y
           grind)
        | exact superpose b0e46 b0e180183
        | exact resolve b0e180183 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e180183
      have b0e187345 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e18816 X0
           have i₂ := b0e180199
           grind)
        | exact superpose b0e180199 b0e18816
        | exact resolve b0e18816 b0e180199
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18816 b0e180199
      have b0e187578 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e187345 X0
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e187345
        | exact resolve b0e187345 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e187345
      have b0e187913 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e21201 y
           have i₂ := b0e187578 y
           grind)
        | exact superpose b0e187578 b0e21201
        | (have j0 := b0e21201 y
           grind)
        | exact resolve b0e21201 b0e187578
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21201 b0e187578
      have b0e187927 : y = (M.op x y) ∨ y = (M.op y y) := by grind
      clear b0e187913
      have b0e187948 : y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e187927
           have i₂ := b0e46 y
           grind)
        | exact superpose b0e46 b0e187927
        | exact resolve b0e187927 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e187927
      have b0e187949 : y = (M.op x y) := by grind
      clear b0e187948
      have b0e191631 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e1933 X0
           have i₂ := b0e187949
           grind)
        | exact superpose b0e187949 b0e1933
        | exact resolve b0e1933 b0e187949
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1933
      have b0e191693 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e53502 X0
           have i₂ := b0e187949
           grind)
        | exact superpose b0e187949 b0e53502
        | exact resolve b0e53502 b0e187949
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53502 b0e187949
      have b0e191897 : False := by grind
      exact b0e191897
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
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
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e34 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (σ y) X0 (σ x) X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 x X0 x X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e35 x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e35
          | exact resolve b1e35 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e68 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op x y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 y X1 X2
             have i₂ := b1e40 X0
             grind)
          | exact superpose b1e40 b1e12
          | exact resolve b1e12 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e145 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e26 X1 X0
             grind)
          | exact superpose b1e26 b1e13
          | exact resolve b1e13 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e549 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) := by
          intro X0 X2
          first
          | (have i₁ := b1e34 x X2
             have i₂ := b1e34 x X0
             grind)
          | (have i₁ := b1e34 X0 x
             have i₂ := b1e34 X0 (M.op X0 (σ y))
             grind)
          | exact superpose b1e34 b1e34
          | exact resolve b1e34 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e621 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e22
             have i₂ := b1e549 (σ x) X0
             grind)
          | (have i₁ := b1e22
             have i₂ := b1e549 X0 (σ x)
             grind)
          | exact superpose b1e549 b1e22
          | exact resolve b1e22 b1e549
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e626 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X1 (M.op (σ y) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X1 (σ y) X2 X3
             have i₂ := b1e549 X1 X0
             grind)
          | (have i₁ := b1e12 X1 (σ y) X2 X3
             have i₂ := b1e549 X0 X1
             grind)
          | exact superpose b1e549 b1e12
          | exact resolve b1e12 b1e549
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e549
        have b1e641 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X1 (M.op (σ y) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e626 X0 X1 x x
             have i₂ := b1e68 X1 x x
             grind)
          | exact superpose b1e68 b1e626
          | exact resolve b1e626 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68 b1e626
        have b1e647 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op X1 (σ y)) := by
          intro X1
          first
          | (have i₁ := b1e641 x X1
             have i₂ := b1e621 x
             grind)
          | exact superpose b1e621 b1e641
          | exact resolve b1e641 b1e621
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e641
        have b1e976 : (σ y) = (k (σ y) (σ y)) := by grind
        have b1e1001 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e976
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e976
          | exact resolve b1e976 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e976
        have b1e1386 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e1001
             grind)
          | exact superpose b1e1001 b1e13
          | exact resolve b1e13 b1e1001
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1001
        have b1e1388 : y = (k y y) := by
          first
          | (have i₁ := b1e1386
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e1386
          | exact resolve b1e1386 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1386
        have b1e1577 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e1388
             grind)
          | exact superpose b1e1388 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e1388
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1388
        have b1e1578 : y = (M.op y y) := by grind
        clear b1e1577
        have b1e1580 : y = (M.op x y) := by
          first
          | (have i₁ := b1e1578
             have i₂ := b1e40 y
             grind)
          | exact superpose b1e40 b1e1578
          | exact resolve b1e1578 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e1578
        have b1e2550 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e145
        have b1e2564 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e2550 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e2550
          | exact resolve b1e2550 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2550
        have b1e4286 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e647 X0
             have i₂ := b1e1580
             grind)
          | exact superpose b1e1580 b1e647
          | exact resolve b1e647 b1e1580
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e647
        have b1e5735 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e4286 (σ x)
             grind)
          | exact superpose b1e4286 b1e19
          | exact resolve b1e19 b1e4286
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4286
        have b1e5746 : (σ y) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e5735
             have i₂ := b1e1580
             grind)
          | exact superpose b1e1580 b1e5735
          | exact resolve b1e5735 b1e1580
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1580 b1e5735
        have b1e5826 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e80 x x
             grind)
          | exact superpose b1e80 b1e21
          | (have j1 := b1e80 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e80 x y
             grind)
          | exact resolve b1e21 b1e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80
        have b1e5949 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e5826
        have b1e19403 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e5949
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e5949
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e5949 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5949
        have b1e19404 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e19403
        have b1e19405 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e19404
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19404
          | exact resolve b1e19404 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19404
        have b1e19406 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e19405
        have b1e19412 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e19406
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19406
          | exact resolve b1e19406 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19406
        have b1e30299 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e2564 x
             have i₂ := b1e19412
             grind)
          | exact superpose b1e19412 b1e2564
          | exact resolve b1e2564 b1e19412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2564 b1e19412
        have b1e30383 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e30299
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e30299
          | exact resolve b1e30299 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30299
        have b1e33169 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e30383
             grind)
          | exact superpose b1e30383 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e30383
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30383
        have b1e33174 : x = (M.op x x) ∨ x = y := by grind
        clear b1e33169
        have b1e33187 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e33174
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e33174
          | exact resolve b1e33174 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33174
        have b1e33188 : x = y := by grind
        clear b1e33187
        have b1e33485 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e621 X0
             have i₂ := b1e33188
             grind)
          | exact superpose b1e33188 b1e621
          | exact resolve b1e621 b1e33188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e621
        have b1e35676 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e5746
             have i₂ := b1e33485 y
             grind)
          | exact superpose b1e33485 b1e5746
          | exact resolve b1e5746 b1e33485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5746 b1e33485
        have b1e35917 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e35676
             have i₂ := b1e33188
             grind)
          | exact superpose b1e33188 b1e35676
          | exact resolve b1e35676 b1e33188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33188 b1e35676
        have b1e35918 : False := by grind
        exact b1e35918
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
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
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
        have b2e29 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b2e12 X0 x X4 X5
             have i₂ := b2e12 X0 x X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 x X0 x X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e31 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e31
          | exact resolve b2e31 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op x y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 y X1 X2
             have i₂ := b2e38 X0
             grind)
          | exact superpose b2e38 b2e12
          | exact resolve b2e12 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e80 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e139 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e1147 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e139
        have b2e1160 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1147 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e1147
          | exact resolve b2e1147 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1147
        have b2e2196 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e80 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e80
        have b2e2197 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e2196
             have r₂ := b2e22
             grind)
          | exact resolve b2e2196 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2196
        have b2e2198 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e2197
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e2197
          | exact resolve b2e2197 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2197
        have b2e2199 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e2198
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e2198
          | exact resolve b2e2198 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e2198
        have b2e2209 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ x) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e29 (σ x) X0 X1 (σ y) X2
             have i₂ := b2e2199
             grind)
          | exact superpose b2e2199 b2e29
          | exact resolve b2e29 b2e2199
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e2221 : ∀ X2 : G, (M.op (σ x) X2) = (M.op (σ x) (M.op x y)) := by
          intro X2
          first
          | (have i₁ := b2e2209 x x X2
             have i₂ := b2e62 (σ x) x x
             grind)
          | exact superpose b2e62 b2e2209
          | exact resolve b2e2209 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62 b2e2209
        have b2e4802 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e2221 X0
             have i₂ := b2e2221 X1
             grind)
          | (have i₁ := b2e2221 x
             have i₂ := b2e2221 (M.op x y)
             grind)
          | exact superpose b2e2221 b2e2221
          | exact resolve b2e2221 b2e2221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2221
        have b2e5411 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) := by
          intro X0
          first
          | (have i₁ := b2e1160 x
             have i₂ := b2e4802 (σ x) X0
             grind)
          | (have i₁ := b2e1160 x
             have i₂ := b2e4802 X0 (σ x)
             grind)
          | exact superpose b2e4802 b2e1160
          | exact resolve b2e1160 b2e4802
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1160
        have b2e5414 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e4802 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e4802 X0 (σ x)
             grind)
          | exact superpose b2e4802 b2e21
          | exact resolve b2e21 b2e4802
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5415 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e2199
             have i₂ := b2e4802 (σ y) X0
             grind)
          | (have i₁ := b2e2199
             have i₂ := b2e4802 X0 (σ y)
             grind)
          | exact superpose b2e4802 b2e2199
          | exact resolve b2e2199 b2e4802
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2199 b2e4802
        have b2e5485 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e5414 x
             have i₂ := b2e5415 x
             grind)
          | exact superpose b2e5415 b2e5414
          | exact resolve b2e5414 b2e5415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5414
        have b2e5487 : x = (k x (τ (σ x))) := by
          first
          | (have i₁ := b2e5411 x
             have i₂ := b2e5415 x
             grind)
          | exact superpose b2e5415 b2e5411
          | exact resolve b2e5411 b2e5415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5411 b2e5415
        have b2e5526 : x = (k x x) := by
          first
          | (have i₁ := b2e5487
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e5487
          | exact resolve b2e5487 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5487
        have b2e5872 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e5526
             grind)
          | exact superpose b2e5526 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e5526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5526
        have b2e5873 : x = (M.op x x) := by grind
        clear b2e5872
        have b2e6346 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e5873
             grind)
          | exact superpose b2e5873 b2e20
          | exact resolve b2e20 b2e5873
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5873
        have b2e6876 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e5485
             have i₂ := b2e6346
             grind)
          | exact superpose b2e6346 b2e5485
          | exact resolve b2e5485 b2e6346
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5485 b2e6346
        have b2e6877 : False := by grind
        exact b2e6877
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
        have b3e43 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b3e12 X0 x X4 X5
             have i₂ := b3e12 X0 x X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 y X0 x X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b3e48 x X2
             have i₂ := b3e48 x X0
             grind)
          | (have i₁ := b3e48 X0 x
             have i₂ := b3e48 X0 (M.op X0 y)
             grind)
          | exact superpose b3e48 b3e48
          | exact resolve b3e48 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e94 : ∀ X0 : G, y = (k y (M.op y X0)) := by
          intro X0
          grind
        have b3e97 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X1 (M.op y X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X1 y X2 X3
             have i₂ := b3e53 X1 X0
             grind)
          | (have i₁ := b3e12 X1 y X2 X3
             have i₂ := b3e53 X0 X1
             grind)
          | exact superpose b3e53 b3e12
          | exact resolve b3e12 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e100 : ∀ X0 : G, y = (M.op y X0) := by
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
        have b3e102 : ∀ X1 X2 X3 : G, (M.op X1 y) = (M.op (M.op X1 X2) X3) := by
          intro X1 X2 X3
          first
          | (have i₁ := b3e97 x X1 X2 X3
             have i₂ := b3e100 x
             grind)
          | exact superpose b3e100 b3e97
          | exact resolve b3e97 b3e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e97
        have b3e104 : y = (k y y) := by
          first
          | (have i₁ := b3e94 x
             have i₂ := b3e100 x
             grind)
          | exact superpose b3e100 b3e94
          | exact resolve b3e94 b3e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e94
        have b3e113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e179 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ y) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e43 (σ x) X0 X1 (σ x) X2
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e43
          | exact resolve b3e43 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e221 : ∀ X2 : G, (M.op (σ y) X2) = (M.op (σ x) y) := by
          intro X2
          first
          | (have i₁ := b3e179 x x X2
             have i₂ := b3e102 (σ x) x x
             grind)
          | exact superpose b3e102 b3e179
          | exact resolve b3e179 b3e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e179
        have b3e4614 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e113 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e113
          | exact resolve b3e113 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e4728 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e113 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e113
        have b3e4729 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e4728 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4728
        have b3e4740 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e4614
        have b3e5155 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e4740
             grind)
          | exact superpose b3e4740 b3e13
          | exact resolve b3e13 b3e4740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e5175 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e5155
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e5155
          | exact resolve b3e5155 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5155
        have b3e6868 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e4729 y
             have i₂ := b3e104
             grind)
          | exact superpose b3e104 b3e4729
          | (have j0 := b3e4729 y
             grind)
          | exact resolve b3e4729 b3e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e104 b3e4729
        have b3e6873 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b3e6868
        have b3e6895 : (σ y) = (M.op (σ x) y) := by
          first
          | (have i₁ := b3e6873
             have i₂ := b3e221 (σ y)
             grind)
          | exact superpose b3e221 b3e6873
          | exact resolve b3e6873 b3e221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e221 b3e6873
        have b3e6948 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e102 (σ x) y x
             have i₂ := b3e6895
             grind)
          | exact superpose b3e6895 b3e102
          | exact resolve b3e102 b3e6895
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102 b3e6895
        have b3e9463 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e5175
             grind)
          | exact superpose b3e5175 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e5175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5175
        have b3e9469 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e9463
        have b3e9476 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e9469
             have r₂ := b3e20
             grind)
          | exact resolve b3e9469 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e9469
        have b3e9941 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e9476
        have b3e10579 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e4740
             have i₂ := b3e9941
             grind)
          | exact superpose b3e9941 b3e4740
          | exact resolve b3e4740 b3e9941
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4740 b3e9941
        have b3e10595 : (σ x) = (σ y) := by grind
        clear b3e10579
        have b3e11264 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e6948 X0
             have i₂ := b3e10595
             grind)
          | exact superpose b3e10595 b3e6948
          | exact resolve b3e6948 b3e10595
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6948
        have b3e11265 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e10595
             grind)
          | exact superpose b3e10595 b3e13
          | exact resolve b3e13 b3e10595
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10595
        have b3e11302 : x = y := by
          first
          | (have i₁ := b3e11265
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e11265
          | exact resolve b3e11265 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11265
        have b3e11559 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e11302
             grind)
          | exact superpose b3e11302 b3e19
          | exact resolve b3e19 b3e11302
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e11570 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e100 X0
             have i₂ := b3e11302
             grind)
          | exact superpose b3e11302 b3e100
          | exact resolve b3e100 b3e11302
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e100 b3e11302
        have b3e11620 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e11559
             have i₂ := b3e11570 x
             grind)
          | exact superpose b3e11570 b3e11559
          | exact resolve b3e11559 b3e11570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11559 b3e11570
        have b3e11623 : False := by grind
        exact b3e11623
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b4e31 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
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
          have b4e36 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op y X1) := by
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
          have b4e37 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 x x
               have i₂ := b4e13 X0 X2 x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
            intro X0 X2
            first
            | (have i₁ := b4e36 x X2
               have i₂ := b4e36 x X0
               grind)
            | (have i₁ := b4e36 X0 x
               have i₂ := b4e36 X0 (M.op X0 y)
               grind)
            | exact superpose b4e36 b4e36
            | exact resolve b4e36 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b4e72 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op X1 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X2 X1 X3
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e13 X0 X1 X2 X3
               have i₂ := b4e18 X0 (M.op X0 X2)
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X2) X3) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X1 X2 X3
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e13 X0 X1 X2 X3
               have i₂ := b4e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e101 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X1 (M.op y X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 y X2 X3
               have i₂ := b4e41 X1 X0
               grind)
            | (have i₁ := b4e13 X1 y X2 X3
               have i₂ := b4e41 X0 X1
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e104 : ∀ X0 : G, y = (M.op y X0) := by
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
          have b4e106 : ∀ X1 X2 X3 : G, (M.op X1 y) = (M.op (M.op X1 X2) X3) := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e101 x X1 X2 X3
               have i₂ := b4e104 x
               grind)
            | exact superpose b4e104 b4e101
            | exact resolve b4e101 b4e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101
          have b4e117 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b4e143 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e27 X1 X0
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e172 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ y) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e31 (σ y) X0 X1 (σ x) X2
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e31
            | exact resolve b4e31 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e193 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k (M.op X0 X3) (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3
            grind
          clear b4e31
          have b4e204 : ∀ X0 X3 : G, (M.op X0 X3) = (k (M.op X0 X3) (M.op X0 y)) := by
            intro X0 X3
            first
            | (have i₁ := b4e193 X0 x x X3
               have i₂ := b4e106 X0 x x
               grind)
            | exact superpose b4e106 b4e193
            | exact resolve b4e193 b4e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193
          have b4e214 : ∀ X2 : G, (M.op (σ y) X2) = (M.op (σ y) y) := by
            intro X2
            first
            | (have i₁ := b4e172 x x X2
               have i₂ := b4e106 (σ y) x x
               grind)
            | exact superpose b4e106 b4e172
            | exact resolve b4e172 b4e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e172
          have b4e360 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e37 X0 X1 y
               have i₂ := b4e104 X0
               grind)
            | exact superpose b4e104 b4e37
            | exact resolve b4e37 b4e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104
          have b4e461 : (σ y) = (M.op (σ y) y) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e214 (σ x)
               grind)
            | exact superpose b4e214 b4e24
            | exact resolve b4e24 b4e214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e531 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e214 X0
               have i₂ := b4e461
               grind)
            | exact superpose b4e461 b4e214
            | exact resolve b4e214 b4e461
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e214 b4e461
          have b4e614 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e37 X0 X1 (σ y)
               have i₂ := b4e531 X0
               grind)
            | exact superpose b4e531 b4e37
            | exact resolve b4e37 b4e531
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e531
          have b4e624 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e614 X0 x
               have i₂ := b4e360 X0 x
               grind)
            | exact superpose b4e360 b4e614
            | exact resolve b4e614 b4e360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e614
          have b4e959 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e624 (σ x)
               grind)
            | exact superpose b4e624 b4e20
            | exact resolve b4e20 b4e624
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e624
          have b4e2945 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e117 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e117
            | exact resolve b4e117 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3030 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X2) = (k X4 X2) ∨ (M.op X4 X0) = (k X4 X0) ∨ (M.op X0 X1) = (M.op X2 X3) ∨ (M.op X2 X4) = X2 ∨ (M.op X0 X4) = X0 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e72 X0 X4 x X1
               have i₂ := b4e72 X2 X4 x X3
               grind)
            | (have i₁ := b4e72 X0 X0 X2 X3
               have i₂ := b4e72 X0 X1 X2 (M.op X2 X0)
               grind)
            | exact superpose b4e72 b4e72
            | (have j0 := b4e72 X2 X4 X2 X3
               have j1 := b4e72 X2 X4 X2 X3
               grind)
            | exact resolve b4e72 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3812 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (M.op (σ X0) X2) X3) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e73 (σ X1) (σ X0) X2 X3
               grind)
            | exact superpose b4e73 b4e19
            | (have j1 := b4e73 (σ X1) (σ X0) X2 X3
               grind)
            | exact resolve b4e19 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e3818 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e3812 X0 X1 x x
               have i₂ := b4e106 (σ X0) x x
               grind)
            | exact superpose b4e106 b4e3812
            | (have j0 := b4e3812 X0 X1 x x
               grind)
            | exact resolve b4e3812 b4e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3812
          have b4e3995 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b4e143
          have b4e4013 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e3995 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e3995
            | exact resolve b4e3995 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3995
          have b4e5550 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e68 X1 X0
               have i₂ := b4e68 X0 X1
               grind)
            | exact superpose b4e68 b4e68
            | (have j0 := b4e68 X1 X0
               have j1 := b4e68 X1 X0
               grind)
            | exact resolve b4e68 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e5589 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op X2 (M.op X3 X2)) ∨ (M.op X2 (σ X0)) = (k X2 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X2) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e72 (σ X0) X2 X3 (σ X1)
               have i₂ := b4e68 X0 X1
               grind)
            | exact superpose b4e68 b4e72
            | (have j0 := b4e72 (σ X0) X2 X2 X3
               have j1 := b4e68 X0 X1
               grind)
            | exact resolve b4e72 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e5653 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ X1) (σ X0)
               have i₂ := b4e68 X1 X0
               grind)
            | exact superpose b4e68 b4e17
            | (have j0 := b4e17 (σ X1) (σ X0)
               have j1 := b4e68 X1 X0
               grind)
            | (have r₁ := b4e17 (σ X1) (σ X1)
               have r₂ := b4e68 X1 X1
               grind)
            | (have r₁ := b4e17 (σ X0) (σ X1)
               have r₂ := b4e68 X0 X1
               grind)
            | exact resolve b4e17 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e5680 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e68 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e5681 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e5680 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5680
          have b4e5683 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e5653 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5653
          have b4e5684 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e5683 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5683
          have b4e5714 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e5684 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e5684
            | (have j0 := b4e5684 X0 X1
               grind)
            | exact resolve b4e5684 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5684
          have b4e5750 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (k X2 (σ X0)) ∨ (σ (k X0 X1)) = (M.op X2 y) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e5589 X0 X1 X2 x
               have i₂ := b4e360 X2 x
               grind)
            | exact superpose b4e360 b4e5589
            | (have j0 := b4e5589 X0 X1 X2 x
               grind)
            | exact resolve b4e5589 b4e360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5589
          have b4e7873 : ∀ X0 : G, (σ (M.op X0 y)) ≠ (σ (M.op X0 y)) ∨ (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b4e5681 (M.op X0 y)
               have i₂ := b4e204 X0 y
               grind)
            | exact superpose b4e204 b4e5681
            | (have j0 := b4e5681 (M.op X0 y)
               grind)
            | exact resolve b4e5681 b4e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e204
          have b4e7878 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e5681 (τ X0)
               have i₂ := b4e27 X0 (τ X0)
               grind)
            | exact superpose b4e27 b4e5681
            | (have j0 := b4e5681 (τ X0)
               grind)
            | exact resolve b4e5681 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5681
          have b4e7881 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
            intro X0
            first
            | (have j0 := b4e7873 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7873
          have b4e7897 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e7878 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e7878
            | (have j0 := b4e7878 X0
               grind)
            | exact resolve b4e7878 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7878
          have b4e7905 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e7897 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e7897
            | (have j0 := b4e7897 X0
               grind)
            | exact resolve b4e7897 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7897
          have b4e9901 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b4e7905 (τ X0)
               have i₂ := b4e2945 X0 X0
               grind)
            | exact superpose b4e2945 b4e7905
            | (have j0 := b4e7905 (τ X0)
               grind)
            | exact resolve b4e7905 b4e2945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7905
          have b4e20421 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b4e5714
          have b4e20507 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e20421 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e20421
            | (have j0 := b4e20421 X0 X1
               grind)
            | exact resolve b4e20421 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20421
          have b4e20508 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e20507 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20507
          have b4e26162 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) y) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e360 (σ X1) (σ X0)
               have i₂ := b4e3818 X1 X0
               grind)
            | exact superpose b4e3818 b4e360
            | (have j1 := b4e3818 X1 X0
               grind)
            | exact resolve b4e360 b4e3818
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3818
          have b4e26191 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) y) := by
            intro X0 X1
            first
            | (have j0 := b4e26162 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26162
          have b4e34917 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e3030 X0 X1 X0 x X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3030
          have b4e34918 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e34917 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34917
          have b4e87148 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 y) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e5750 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5750
          have b4e87150 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 y) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e87148 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87148
          have b4e87234 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 y) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e87150 X0 X1
               have j1 := b4e34918 (σ X0) X1 x
               grind)
            | (have r₁ := b4e87150 X0 (σ (k X0 X0))
               have r₂ := b4e34918 (σ (k X0 X0)) X1 y
               grind)
            | (have r₁ := b4e87150 X0 X1
               have r₂ := b4e34918 (σ X0) X1 (σ X0)
               grind)
            | (have r₁ := b4e87150 X0 x
               have r₂ := b4e34918 (σ X0) X1 x
               grind)
            | exact resolve b4e87150 b4e34918
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34918 b4e87150
          have b4e93159 : ∀ X0 : G, (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) = (M.op (σ (M.op X0 y)) y) := by
            intro X0
            first
            | (have i₁ := b4e360 (σ (M.op X0 y)) (σ (M.op X0 y))
               have i₂ := b4e7881 X0
               grind)
            | exact superpose b4e7881 b4e360
            | exact resolve b4e360 b4e7881
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e360
          have b4e93216 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) y) := by
            intro X0
            first
            | (have i₁ := b4e93159 X0
               have i₂ := b4e7881 X0
               grind)
            | exact superpose b4e7881 b4e93159
            | exact resolve b4e93159 b4e7881
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7881 b4e93159
          have b4e93760 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e5550 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e5550
            | exact resolve b4e5550 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5550
          have b4e95317 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e93760 X0 X1
               have i₂ := b4e27 X0 X1
               grind)
            | exact superpose b4e27 b4e93760
            | (have j0 := b4e93760 X0 X1
               grind)
            | exact resolve b4e93760 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93760
          have b4e95570 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e95317 X0 X1
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e95317
            | (have j0 := b4e95317 X0 X1
               grind)
            | exact resolve b4e95317 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e95317
          have b4e95664 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b4e95570 X0 X1
               have j1 := b4e17 X0 (σ X1)
               grind)
            | (have r₁ := b4e95570 (σ X1) X1
               have r₂ := b4e17 (σ X1) (σ X1)
               grind)
            | (have r₁ := b4e95570 (M.op (M.op (σ X1) (σ X1)) X0) X1
               have r₂ := b4e17 X0 (M.op (σ X1) (σ X1))
               grind)
            | (have r₁ := b4e95570 X0 X1
               have r₂ := b4e17 X0 (σ X1)
               grind)
            | exact resolve b4e95570 b4e17
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e95570
          have b4e100379 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e106 (σ (M.op X0 y)) y x
               have i₂ := b4e93216 X0
               grind)
            | exact superpose b4e93216 b4e106
            | exact resolve b4e106 b4e93216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93216
          have b4e162983 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e20508 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e20508
            | exact resolve b4e20508 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e163309 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (σ (k (M.op X0 y) X1)) ∨ (σ (M.op X0 y)) = (σ (k (M.op X0 y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e100379 X0 (σ X1)
               have i₂ := b4e20508 X1 (M.op X0 y)
               grind)
            | exact superpose b4e20508 b4e100379
            | (have j1 := b4e20508 X1 (M.op X0 y)
               grind)
            | exact resolve b4e100379 b4e20508
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e163337 : ∀ X0 X1 X2 : G, (M.op (σ X0) y) = (M.op (σ (k X0 X1)) X2) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e106 (σ X0) (σ X1) X2
               have i₂ := b4e20508 X1 X0
               grind)
            | exact superpose b4e20508 b4e106
            | (have j1 := b4e20508 X1 X0
               grind)
            | exact resolve b4e106 b4e20508
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20508
          have b4e163410 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (σ (k (M.op X0 y) X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e163309 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e163309
          have b4e163574 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e162983 X0 X1
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e162983
            | (have j0 := b4e162983 X0 X1
               grind)
            | exact resolve b4e162983 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e162983
          have b4e163615 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e163574 X0 X1
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e163574
            | (have j0 := b4e163574 X0 X1
               grind)
            | exact resolve b4e163574 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e163574
          have b4e163824 : ∀ X0 X1 : G, (k (M.op X0 y) X1) = (τ (σ (M.op X0 y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (M.op X0 y) X1)
               have i₂ := b4e163410 X0 X1
               grind)
            | exact superpose b4e163410 b4e14
            | exact resolve b4e14 b4e163410
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e163410
          have b4e164175 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e163824 X0 X1
               have i₂ := b4e14 (M.op X0 y)
               grind)
            | exact superpose b4e14 b4e163824
            | exact resolve b4e163824 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e163824
          have b4e258494 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e163615 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e163615
            | exact resolve b4e163615 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e258580 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e117 X0 X1
               have i₂ := b4e163615 X0 X1
               grind)
            | exact superpose b4e163615 b4e117
            | (have j1 := b4e163615 X0 X1
               grind)
            | exact resolve b4e117 b4e163615
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e163615
          have b4e258937 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 y) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e87234 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e87234
            | (have j0 := b4e87234 (τ X0) X1
               grind)
            | exact resolve b4e87234 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87234
          have b4e260821 : ∀ X0 X1 : G, (M.op X1 y) = (k (σ (τ X0)) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e258937 X0 X1
               have i₂ := b4e27 X0 (τ X0)
               grind)
            | exact superpose b4e27 b4e258937
            | (have j0 := b4e258937 X0 X1
               grind)
            | exact resolve b4e258937 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e258937
          have b4e261071 : ∀ X0 X1 : G, (M.op X1 y) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e260821 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e260821
            | (have j0 := b4e260821 X0 X1
               grind)
            | exact resolve b4e260821 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e260821
          have b4e261813 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e258494 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e258494
          have b4e264192 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 y) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e261813 (M.op X0 X1) X2
               have i₂ := b4e106 X0 X1 X2
               grind)
            | exact superpose b4e106 b4e261813
            | (have j0 := b4e261813 (M.op X0 X1) X2
               grind)
            | (have r₁ := b4e261813 (M.op X1 y) x
               have r₂ := b4e106 X1 y x
               grind)
            | exact resolve b4e261813 b4e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e261813
          have b4e306302 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e258580 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e258580
            | exact resolve b4e258580 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e258580
          have b4e306642 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e306302 X0 X1
               have i₂ := b4e2945 X0 X1
               grind)
            | exact superpose b4e2945 b4e306302
            | (have j0 := b4e306302 X0 X1
               grind)
            | exact resolve b4e306302 b4e2945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e306302
          have b4e307765 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (k (τ (M.op X0 X1)) (τ X2)) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2945 X2 (k X0 X1)
               have i₂ := b4e306642 X1 X0
               grind)
            | exact superpose b4e306642 b4e2945
            | (have j1 := b4e306642 X1 X0
               grind)
            | exact resolve b4e2945 b4e306642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e306642
          have b4e307862 : ∀ X0 X1 X2 : G, (τ (k (k X0 X1) X2)) = (τ (k (M.op X0 X1) X2)) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e307765 X0 X1 X2
               have i₂ := b4e2945 X2 (M.op X0 X1)
               grind)
            | exact superpose b4e2945 b4e307765
            | (have j0 := b4e307765 X0 X1 X2
               grind)
            | exact resolve b4e307765 b4e2945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e307765
          have b4e346400 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e95664 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e95664
            | exact resolve b4e95664 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e95664
          have b4e393672 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) y) = (M.op (σ (τ (k X0 X1))) X2) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e163337 (τ X1) (τ X0) X2
               have i₂ := b4e2945 X0 X1
               grind)
            | exact superpose b4e2945 b4e163337
            | exact resolve b4e163337 b4e2945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e163337
          have b4e394110 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) y) = (M.op (k X0 X1) X2) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e393672 X0 X1 X2
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e393672
            | (have j0 := b4e393672 X0 X1 X2
               grind)
            | exact resolve b4e393672 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e393672
          have b4e394154 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (k X0 X1) X2) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e394110 X0 X1 X2
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e394110
            | (have j0 := b4e394110 X0 X1 X2
               grind)
            | exact resolve b4e394110 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e394110
          have b4e394170 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X0 y) = (M.op (k X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e394154 X0 X1 X2
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e394154
            | (have j0 := b4e394154 X0 X1 X2
               grind)
            | exact resolve b4e394154 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e394154
          have b4e394175 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (k X0 X1) X2) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e394170 X0 X1 X2
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e394170
            | (have j0 := b4e394170 X0 X1 X2
               grind)
            | exact resolve b4e394170 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e394170
          have b4e394665 : ∀ X0 X1 X2 X3 : G, (M.op X0 y) ≠ (M.op (k X0 X1) X2) ∨ (M.op (k X0 X1) X2) = (k (M.op (k X0 X1) X2) X3) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e264192 (k X0 X1) X2 X3
               have i₂ := b4e394175 X0 X1 y
               grind)
            | exact superpose b4e394175 b4e264192
            | (have j0 := b4e264192 (k X0 X1) X2 X3
               have j1 := b4e394175 (M.op (k X0 X1) X2) X3 X2
               grind)
            | exact resolve b4e264192 b4e394175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e264192
          have b4e394674 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) X2) = (k (M.op (k X0 X1) X2) X3) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b4e394665 X0 X1 X2 X3
               have j1 := b4e394175 (M.op (k X0 X1) X2) X3 X2
               grind)
            | (have r₁ := b4e394665 X0 X1 X2 X3
               have r₂ := b4e394175 X0 X1 X2
               grind)
            | exact resolve b4e394665 b4e394175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e394175 b4e394665
          have b4e494689 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (σ (τ (k (M.op X0 X1) X2))) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e15 (k (k X0 X1) X2)
               have i₂ := b4e307862 X0 X1 X2
               grind)
            | exact superpose b4e307862 b4e15
            | (have j1 := b4e307862 X0 X1 X2
               grind)
            | exact resolve b4e15 b4e307862
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e307862
          have b4e494753 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = (k (k X0 X1) X2) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e494689 X0 X1 X2
               have i₂ := b4e15 (k (M.op X0 X1) X2)
               grind)
            | exact superpose b4e15 b4e494689
            | (have j0 := b4e494689 X0 X1 X2
               grind)
            | exact resolve b4e494689 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e494689
          have b4e495315 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op X0 X1) (M.op (k X0 X1) (k X0 X1))) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          clear b4e494753
          have b4e574618 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e261071 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e261071
          have b4e583617 : ∀ X0 X1 : G, (M.op X0 y) ≠ (M.op (M.op X0 X1) y) ∨ (M.op (M.op X0 X1) y) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e574618 (M.op X1 x)
               have i₂ := b4e106 X1 x (M.op X1 x)
               grind)
            | exact superpose b4e106 b4e574618
            | (have j0 := b4e574618 (M.op X0 X1)
               grind)
            | exact resolve b4e574618 b4e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e574618
          have b4e583665 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have j0 := b4e583617 X0 X1
               grind)
            | (have r₁ := b4e583617 X1 x
               have r₂ := b4e106 X1 x y
               grind)
            | exact resolve b4e583617 b4e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e583617
          have b4e583676 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e583665 X0 X1
               have i₂ := b4e106 X0 X1 y
               grind)
            | exact superpose b4e106 b4e583665
            | (have j0 := b4e583665 X0 X1
               grind)
            | exact resolve b4e583665 b4e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e583665
          have b4e583813 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X2) = (M.op (k X0 X1) y) ∨ (k X0 X1) = X0 ∨ (M.op (k X0 X1) X2) = (M.op (k X0 X1) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e394674 X0 X1 X2 (M.op (k X0 X1) X2)
               have i₂ := b4e583676 (k X0 X1) X2
               grind)
            | exact superpose b4e583676 b4e394674
            | (have j0 := b4e394674 X0 X1 X2 x
               have j1 := b4e583676 (k X0 X1) X2
               grind)
            | exact resolve b4e394674 b4e583676
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e394674
          have b4e584168 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X2) = (M.op (k X0 X1) y) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e583813 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e583813
          have b4e586778 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) X2) = (M.op (k X0 X1) X3) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e584168 X0 X1 X2
               have i₂ := b4e584168 X0 X1 X3
               grind)
            | (have i₁ := b4e584168 X0 X1 X2
               have i₂ := b4e584168 X0 X1 y
               grind)
            | exact superpose b4e584168 b4e584168
            | (have j0 := b4e584168 X0 X1 X2
               have j1 := b4e584168 X0 X1 X2
               grind)
            | exact resolve b4e584168 b4e584168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e584168
          have b4e587064 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) X2) = (M.op (k X0 X1) X3) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b4e586778 X0 X1 X2 X3
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e586778
          have b4e737393 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 y) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e26191 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e26191
            | exact resolve b4e26191 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26191
          have b4e737534 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 y) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e737393 X0 X1
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e737393
            | (have j0 := b4e737393 X0 X1
               grind)
            | exact resolve b4e737393 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e737393
          have b4e737573 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e737534 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e737534
            | exact resolve b4e737534 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e737534
          have b4e811628 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X0 X1) (M.op (k X0 X1) X2)) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e495315 X0 X1
               have i₂ := b4e587064 X0 X1 (k X0 X1) X2
               grind)
            | (have i₁ := b4e495315 X0 X1
               have i₂ := b4e587064 X0 X1 X2 (k X0 X1)
               grind)
            | exact superpose b4e587064 b4e495315
            | (have j0 := b4e495315 X0 X1
               have j1 := b4e587064 X0 X1 X2 x
               grind)
            | exact resolve b4e495315 b4e587064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e495315 b4e587064
          have b4e811763 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X0 X1) (M.op (k X0 X1) X2)) ∨ (k X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e811628 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e811628
          have b4e813018 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 X1) X2) = (k (M.op X0 y) (M.op (k (M.op X0 X1) X2) X3)) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e811763 (M.op X0 X1) X2 X3
               have i₂ := b4e106 X0 X1 X2
               grind)
            | exact superpose b4e106 b4e811763
            | (have j0 := b4e811763 (M.op X0 X1) X2 X2
               grind)
            | exact resolve b4e811763 b4e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e811763
          have b4e813374 : ∀ X0 X1 X2 : G, (M.op X0 y) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e813018 X0 X1 X2 x
               have i₂ := b4e164175 X0 (M.op (k (M.op X0 X1) X2) x)
               grind)
            | exact superpose b4e164175 b4e813018
            | (have j0 := b4e813018 X0 X1 X2 x
               grind)
            | exact resolve b4e813018 b4e164175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e164175 b4e813018
          have b4e814198 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e813374 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e813374
          have b4e1490801 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          clear b4e346400
          have b4e1490820 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e1490801 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1490801
          have b4e1491034 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e4013 X1
               have i₂ := b4e1490820 (σ X1) X0
               grind)
            | (have i₁ := b4e4013 X0
               have i₂ := b4e1490820 X0 (M.op (σ X0) (σ X0))
               grind)
            | exact superpose b4e1490820 b4e4013
            | (have j1 := b4e1490820 (σ X1) X0
               grind)
            | exact resolve b4e4013 b4e1490820
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4013 b4e1490820
          have b4e1492208 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (τ X0) = (k (τ X0) X1) ∨ (k X1 (τ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e117 X0 X1
               have i₂ := b4e1491034 X0 X1
               grind)
            | exact superpose b4e1491034 b4e117
            | (have j1 := b4e1491034 X0 X1
               grind)
            | exact resolve b4e117 b4e1491034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e117 b4e1491034
          have b4e1515424 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X1) = (k (τ X1) (τ X0)) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1492208 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1492208
            | (have j0 := b4e1492208 X1 (τ X0)
               grind)
            | exact resolve b4e1492208 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1492208
          have b4e1515438 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1515424 X0 X1
               have i₂ := b4e2945 X0 X1
               grind)
            | exact superpose b4e2945 b4e1515424
            | (have j0 := b4e1515424 X0 X1
               grind)
            | exact resolve b4e1515424 b4e2945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1515424
          have b4e1515441 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e1515438 X0 X1
               have i₂ := b4e2945 X1 X0
               grind)
            | exact superpose b4e2945 b4e1515438
            | (have j0 := b4e1515438 X0 X1
               grind)
            | exact resolve b4e1515438 b4e2945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2945 b4e1515438
          have b4e1515449 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e1515441 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1515441
          have b4e1515450 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e1515449 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1515449
          have b4e1515468 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e9901 X0
               have i₂ := b4e1515450 X0
               grind)
            | exact superpose b4e1515450 b4e9901
            | (have j0 := b4e9901 X0
               have j1 := b4e1515450 X0
               grind)
            | (have r₁ := b4e9901 X0
               have r₂ := b4e1515450 X0
               grind)
            | exact resolve b4e9901 b4e1515450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9901 b4e1515450
          have b4e1515540 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e1515468 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1515468
          have b4e1515653 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ X0) y) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e106 (τ X0) (τ X0) X1
               have i₂ := b4e1515540 X0
               grind)
            | exact superpose b4e1515540 b4e106
            | (have j1 := b4e1515540 X0
               grind)
            | exact resolve b4e106 b4e1515540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1516827 : ∀ X0 : G, (τ X0) = (M.op (τ X0) y) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e1515540 X0
               have i₂ := b4e1515653 X0 (τ X0)
               grind)
            | exact superpose b4e1515653 b4e1515540
            | (have j0 := b4e1515540 X0
               have j1 := b4e1515653 X0 x
               grind)
            | exact resolve b4e1515540 b4e1515653
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1515540 b4e1515653
          have b4e1517043 : ∀ X0 : G, (τ X0) = (M.op (τ X0) y) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e1516827 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1516827
          have b4e1517192 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e100379 (τ X0) X1
               have i₂ := b4e1517043 X0
               grind)
            | exact superpose b4e1517043 b4e100379
            | (have j1 := b4e1517043 X0
               grind)
            | exact resolve b4e100379 b4e1517043
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100379 b4e1517043
          have b4e1517693 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1517192 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1517192
            | (have j0 := b4e1517192 X0 X1
               grind)
            | exact resolve b4e1517192 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1517192
          have b4e1519809 : ∀ X0 X2 : G, (M.op X0 y) ≠ X0 ∨ (M.op X0 y) = (k X0 X2) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X2
            first
            | (have i₁ := b4e814198 X0 x X2
               have i₂ := b4e1517693 X0 x
               grind)
            | exact superpose b4e1517693 b4e814198
            | (have j1 := b4e1517693 X0 x
               grind)
            | exact resolve b4e814198 b4e1517693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1520994 : ∀ X0 X2 : G, (M.op X0 y) = (k X0 X2) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X2
            first
            | (have j0 := b4e1519809 X0 X2
               have j1 := b4e1517693 X0 x
               grind)
            | (have r₁ := b4e1519809 X0 X2
               have r₂ := b4e1517693 X0 y
               grind)
            | exact resolve b4e1519809 b4e1517693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1517693 b4e1519809
          have b4e1532380 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e1520994 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1520994
          have b4e1532400 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e1532380 X0
               have j1 := b4e737573 X0 X0
               grind)
            | (have r₁ := b4e1532380 X0
               have r₂ := b4e737573 X0 X0
               grind)
            | (have r₁ := b4e1532380 y
               have r₂ := b4e737573 y y
               grind)
            | exact resolve b4e1532380 b4e737573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e737573 b4e1532380
          have b4e1534774 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e1532400 (σ X0)
               grind)
            | exact superpose b4e1532400 b4e19
            | exact resolve b4e19 b4e1532400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1535057 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1534774 X0
               have i₂ := b4e1532400 X0
               grind)
            | exact superpose b4e1532400 b4e1534774
            | exact resolve b4e1534774 b4e1532400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1534774
          have b4e1538000 : ∀ X0 : G, (M.op (σ X0) y) = (k (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ X0) y) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e583676 (σ X0) (σ X0)
               have i₂ := b4e1535057 X0
               grind)
            | exact superpose b4e1535057 b4e583676
            | exact resolve b4e583676 b4e1535057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e583676
          have b4e1538065 : ∀ X0 X1 : G, (M.op (σ X0) y) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) y) = (k (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e814198 (σ X0) (σ X0) x
               have i₂ := b4e1535057 X0
               grind)
            | exact superpose b4e1535057 b4e814198
            | exact resolve b4e814198 b4e1535057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e814198 b4e1535057
          have b4e1538215 : ∀ X0 : G, (M.op (σ X0) y) = (k (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b4e1538000 X0
               have j1 := b4e1538065 X0 (σ (M.op X0 X0))
               grind)
            | (have r₁ := b4e1538000 X0
               have r₂ := b4e1538065 X0 x
               grind)
            | exact resolve b4e1538000 b4e1538065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1538000 b4e1538065
          have b4e1538390 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e1538215 X0
               have i₂ := b4e19 (M.op X0 X0) (M.op X0 X0)
               grind)
            | exact superpose b4e19 b4e1538215
            | exact resolve b4e1538215 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1538215
          have b4e1538465 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e1538390 X0
               have i₂ := b4e1532400 (M.op X0 X0)
               grind)
            | exact superpose b4e1532400 b4e1538390
            | exact resolve b4e1538390 b4e1532400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1532400 b4e1538390
          have b4e1538491 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e1538465 X0
               have i₂ := b4e106 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e106 b4e1538465
            | exact resolve b4e1538465 b4e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e106 b4e1538465
          have b4e1539298 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e959
               have i₂ := b4e1538491 x
               grind)
            | exact superpose b4e1538491 b4e959
            | (have r₁ := b4e959
               have r₂ := b4e1538491 x
               grind)
            | exact resolve b4e959 b4e1538491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e959 b4e1538491
          have b4e1539430 : False := by grind
          exact b4e1539430
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b5e32 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op y X1) := by
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
          have b5e35 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 x x
               have i₂ := b5e13 X0 X2 x x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X0 X4 X1 (M.op x (M.op X0 X1))
               have i₂ := b5e13 (M.op X0 X1) x X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
            intro X0 X2
            first
            | (have i₁ := b5e32 x X2
               have i₂ := b5e32 x X0
               grind)
            | (have i₁ := b5e32 X0 x
               have i₂ := b5e32 X0 (M.op X0 y)
               grind)
            | exact superpose b5e32 b5e32
            | exact resolve b5e32 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e93 : ∀ X0 X1 : G, y ≠ (M.op y X0) ∨ y = (M.op X1 X1) ∨ (k X1 y) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X1 y
               have i₂ := b5e39 X1 X0
               grind)
            | (have i₁ := b5e17 X1 y
               have i₂ := b5e39 X0 X1
               grind)
            | exact superpose b5e39 b5e17
            | (have j0 := b5e17 X1 y
               grind)
            | exact resolve b5e17 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X1 (M.op y X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 y X2 X3
               have i₂ := b5e39 X1 X0
               grind)
            | (have i₁ := b5e13 X1 y X2 X3
               have i₂ := b5e39 X0 X1
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e98 : ∀ X0 : G, y = (M.op y X0) := by
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
          have b5e100 : ∀ X1 X2 X3 : G, (M.op X1 y) = (M.op (M.op X1 X2) X3) := by
            intro X1 X2 X3
            first
            | (have i₁ := b5e95 x X1 X2 X3
               have i₂ := b5e98 x
               grind)
            | exact superpose b5e98 b5e95
            | exact resolve b5e95 b5e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95
          have b5e101 : ∀ X1 : G, y = (M.op X1 X1) ∨ (k X1 y) = X1 := by
            intro X1
            first
            | (have j0 := b5e93 x X1
               grind)
            | (have r₁ := b5e93 x X1
               have r₂ := b5e98 x
               grind)
            | exact resolve b5e93 b5e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93
          have b5e137 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e340 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 X0 X1 y
               have i₂ := b5e98 X0
               grind)
            | exact superpose b5e98 b5e35
            | exact resolve b5e35 b5e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e98
          have b5e932 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X0 X2) X3) ∨ (M.op (M.op X0 X2) X3) = (M.op X4 X4) ∨ (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e17 X4 (M.op (M.op X0 X2) X3)
               have i₂ := b5e36 X0 X2 X3 X4 X1
               grind)
            | exact superpose b5e36 b5e17
            | (have j0 := b5e17 X4 (M.op (M.op X0 X2) X3)
               grind)
            | exact resolve b5e17 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e961 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 X2) X3) = (M.op X4 X4) ∨ (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
            intro X0 X2 X3 X4
            first
            | (have j0 := b5e932 X0 x X2 X3 X4
               grind)
            | (have r₁ := b5e932 X0 x X2 X3 X4
               have r₂ := b5e13 X0 x X2 X3
               grind)
            | exact resolve b5e932 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e932
          have b5e1048 : ∀ X0 X2 X3 X4 : G, (M.op X0 y) = (M.op X4 X4) ∨ (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e961 X0 X2 X3 X4
               have i₂ := b5e100 X0 X2 X3
               grind)
            | exact superpose b5e100 b5e961
            | (have j0 := b5e961 X0 X2 X3 X4
               grind)
            | exact resolve b5e961 b5e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e961
          have b5e1098 : ∀ X0 X4 : G, (k X4 (M.op X0 y)) = X4 ∨ (M.op X0 y) = (M.op X4 X4) := by
            intro X0 X4
            first
            | (have i₁ := b5e1048 X0 x x X4
               have i₂ := b5e100 X0 x x
               grind)
            | exact superpose b5e100 b5e1048
            | (have j0 := b5e1048 X0 x x X4
               grind)
            | exact resolve b5e1048 b5e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1048
          have b5e2217 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            grind
          clear b5e101
          have b5e2256 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e2217 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2217
          have b5e2281 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e69 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e2282 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e2281
               have r₂ := b5e24
               grind)
            | exact resolve b5e2281 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2281
          have b5e2283 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e2282
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e2282
            | exact resolve b5e2282 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2282
          have b5e2284 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e2283
               have i₂ := b5e2256 x
               grind)
            | exact superpose b5e2256 b5e2283
            | exact resolve b5e2283 b5e2256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2256 b5e2283
          have b5e4306 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e2284
               grind)
            | exact superpose b5e2284 b5e20
            | exact resolve b5e20 b5e2284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4330 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) y) := by
            intro X0
            first
            | (have i₁ := b5e100 (σ x) (σ y) X0
               have i₂ := b5e2284
               grind)
            | exact superpose b5e2284 b5e100
            | exact resolve b5e100 b5e2284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e100
          have b5e4503 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e62 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e4504 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e4503 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4503
          have b5e5472 : (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b5e2284
               have i₂ := b5e4330 (σ y)
               grind)
            | exact superpose b5e4330 b5e2284
            | exact resolve b5e2284 b5e4330
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2284 b5e4330
          have b5e5687 : ∀ X0 X1 : G, (k X1 (M.op X0 y)) = X1 ∨ (k X1 (M.op X0 y)) = X1 := by
            intro X0 X1
            grind
          clear b5e1098
          have b5e5742 : ∀ X0 X1 : G, (k X1 (M.op X0 y)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e5687 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5687
          have b5e5940 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e5742 (σ x) X0
               have i₂ := b5e5472
               grind)
            | exact superpose b5e5472 b5e5742
            | exact resolve b5e5742 b5e5472
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5472 b5e5742
          have b5e6531 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) := by
            intro X0
            first
            | (have i₁ := b5e137 X0 (σ x)
               have i₂ := b5e5940 (σ X0)
               grind)
            | exact superpose b5e5940 b5e137
            | exact resolve b5e137 b5e5940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5940
          have b5e6534 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b5e6531 X0
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e6531
            | exact resolve b5e6531 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6531
          have b5e6536 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e6534 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e6534
            | exact resolve b5e6534 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6534
          have b5e6601 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ x)) := by
            intro X0
            first
            | (have i₁ := b5e137 X0 x
               have i₂ := b5e6536 (σ X0)
               grind)
            | exact superpose b5e6536 b5e137
            | exact resolve b5e137 b5e6536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e137 b5e6536
          have b5e6605 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e6601 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e6601
            | exact resolve b5e6601 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6601
          have b5e7215 : (σ (τ x)) ≠ (σ (τ x)) ∨ (σ (τ x)) = (M.op (σ (τ x)) (σ (τ x))) := by
            first
            | (have i₁ := b5e4504 (τ x)
               have i₂ := b5e6605 (τ x)
               grind)
            | exact superpose b5e6605 b5e4504
            | (have j0 := b5e4504 (τ x)
               grind)
            | exact resolve b5e4504 b5e6605
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4504 b5e6605
          have b5e7235 : (σ (τ x)) = (M.op (σ (τ x)) (σ (τ x))) := by grind
          clear b5e7215
          have b5e7250 : x = (M.op x x) := by
            first
            | (have i₁ := b5e7235
               have i₂ := b5e15 x
               grind)
            | exact superpose b5e15 b5e7235
            | exact resolve b5e7235 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7235
          have b5e7282 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b5e340 x x
               have i₂ := b5e7250
               grind)
            | exact superpose b5e7250 b5e340
            | exact resolve b5e340 b5e7250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e340
          have b5e7285 : x = (M.op x y) := by
            first
            | (have i₁ := b5e7282
               have i₂ := b5e7250
               grind)
            | exact superpose b5e7250 b5e7282
            | exact resolve b5e7282 b5e7250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7250 b5e7282
          have b5e7411 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e4306
               have i₂ := b5e7285
               grind)
            | exact superpose b5e7285 b5e4306
            | exact resolve b5e4306 b5e7285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4306 b5e7285
          have b5e7449 : False := by grind
          exact b5e7449
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
        have b6e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e35 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        clear b6e28
        have b6e39 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e35 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e35
          | exact resolve b6e35 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e81 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e88 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ y) = X0 ∨ (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e22
             have i₂ := b6e17 (σ x) X0
             grind)
          | (have i₁ := b6e22
             have i₂ := b6e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b6e17 b6e22
          | (have j1 := b6e17 (σ x) X0
             grind)
          | exact resolve b6e22 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e90 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e81
             have r₂ := b6e20
             grind)
          | exact resolve b6e81 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e93 : x = (M.op x y) := by
          first
          | (have r₁ := b6e90
             have r₂ := b6e21
             grind)
          | exact resolve b6e90 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e96 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 x X0 y X1
             have i₂ := b6e93
             grind)
          | exact superpose b6e93 b6e12
          | exact resolve b6e12 b6e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e195 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b6e96 x X2
             have i₂ := b6e96 x X0
             grind)
          | (have i₁ := b6e96 X0 x
             have i₂ := b6e96 X0 (M.op X0 x)
             grind)
          | exact superpose b6e96 b6e96
          | exact resolve b6e96 b6e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e96
        have b6e304 : ∀ X0 : G, y ≠ (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e20
             have i₂ := b6e195 x X0
             grind)
          | (have i₁ := b6e20
             have i₂ := b6e195 X0 x
             grind)
          | exact superpose b6e195 b6e20
          | exact resolve b6e20 b6e195
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e307 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e93
             have i₂ := b6e195 y X0
             grind)
          | (have i₁ := b6e93
             have i₂ := b6e195 X0 y
             grind)
          | exact superpose b6e195 b6e93
          | exact resolve b6e93 b6e195
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e93 b6e195
        have b6e308 : x ≠ y := by
          first
          | (have i₁ := b6e304 x
             have i₂ := b6e307 x
             grind)
          | exact superpose b6e307 b6e304
          | exact resolve b6e304 b6e307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e304
        have b6e3820 : (σ x) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ (M.op (τ (σ x)) (τ (σ x)))) (σ x)) := by
          first
          | (have i₁ := b6e88 (σ (M.op (τ (σ x)) (τ (σ x))))
             have i₂ := b6e39 (σ x)
             grind)
          | exact superpose b6e39 b6e88
          | (have j0 := b6e88 (σ (M.op (τ (σ x)) (τ (σ x))))
             grind)
          | exact resolve b6e88 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39 b6e88
        have b6e3823 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ (M.op (τ (σ x)) (τ (σ x)))) (σ x)) := by
          first
          | (have i₁ := b6e3820
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3820
          | exact resolve b6e3820 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3820
        have b6e3836 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ (M.op (τ (σ x)) (τ (σ x)))) (σ x)) := by
          first
          | (have i₁ := b6e3823
             have i₂ := b6e307 x
             grind)
          | exact superpose b6e307 b6e3823
          | exact resolve b6e3823 b6e307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3823
        have b6e3839 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ (M.op (τ (σ x)) (τ (σ x)))) (σ x)) := by
          first
          | (have i₁ := b6e3836
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e3836
          | exact resolve b6e3836 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3836
        have b6e3841 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ (M.op (τ (σ x)) (τ (σ x)))) (σ x)) := by
          first
          | (have i₁ := b6e3839
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3839
          | exact resolve b6e3839 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3839
        have b6e3843 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ (M.op (τ (σ x)) (τ (σ x)))) (σ x)) := by
          first
          | (have i₁ := b6e3841
             have i₂ := b6e307 x
             grind)
          | exact superpose b6e307 b6e3841
          | exact resolve b6e3841 b6e307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3841
        have b6e3844 : (σ x) = (σ y) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ (M.op (τ (σ x)) (τ (σ x)))) (σ x)) := by grind
        clear b6e3843
        have b6e3847 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3844
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3844
          | exact resolve b6e3844 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3844
        have b6e3849 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3847
             have i₂ := b6e307 x
             grind)
          | exact superpose b6e307 b6e3847
          | exact resolve b6e3847 b6e307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e307 b6e3847
        have b6e3851 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3849
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e3849
          | exact resolve b6e3849 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3849
        have b6e3852 : (σ x) = (σ y) := by grind
        clear b6e3851
        have b6e4617 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e3852
             grind)
          | exact superpose b6e3852 b6e13
          | exact resolve b6e13 b6e3852
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3852
        have b6e4618 : x = y := by
          first
          | (have i₁ := b6e4617
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e4617
          | exact resolve b6e4617 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4617
        have b6e4624 : False := by grind
        exact b6e4624
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b7e33 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ y) X1) := by
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
          have b7e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
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
          have b7e49 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e48
               have r₂ := b7e23
               grind)
            | exact resolve b7e48 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e50 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e49
            | exact resolve b7e49 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e53 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e14
            | exact resolve b7e14 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e54 : x = (k x y) := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e53
            | exact resolve b7e53 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e72 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e73 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e72
               have r₂ := b7e21
               grind)
            | exact resolve b7e72 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e75 : x = (M.op x y) := by
            first
            | (have r₁ := b7e73
               have r₂ := b7e22
               grind)
            | exact resolve b7e73 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e156 : ∀ X0 : G, (M.op y x) = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e36 y X0 x
               have i₂ := b7e75
               grind)
            | exact superpose b7e75 b7e36
            | exact resolve b7e36 b7e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e315 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) := by
            intro X0 X2
            first
            | (have i₁ := b7e33 x X2
               have i₂ := b7e33 x X0
               grind)
            | (have i₁ := b7e33 X0 x
               have i₂ := b7e33 X0 (M.op X0 (σ y))
               grind)
            | exact superpose b7e33 b7e33
            | exact resolve b7e33 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e980 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (σ y) X0)) := by
            intro X0
            grind
          have b7e1002 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e24
               have i₂ := b7e315 (σ x) X0
               grind)
            | (have i₁ := b7e24
               have i₂ := b7e315 X0 (σ x)
               grind)
            | exact superpose b7e315 b7e24
            | exact resolve b7e24 b7e315
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e315
          have b7e1014 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e980 x
               have i₂ := b7e1002 x
               grind)
            | exact superpose b7e1002 b7e980
            | exact resolve b7e980 b7e1002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e980 b7e1002
          have b7e1033 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e1014
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e1014
            | exact resolve b7e1014 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1014
          have b7e1615 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1033
               grind)
            | exact superpose b7e1033 b7e14
            | exact resolve b7e14 b7e1033
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1033
          have b7e1617 : y = (k y y) := by
            first
            | (have i₁ := b7e1615
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1615
            | exact resolve b7e1615 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1615
          have b7e1636 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e1617
               grind)
            | exact superpose b7e1617 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e1617
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1617
          have b7e1637 : y = (M.op y y) := by grind
          clear b7e1636
          have b7e1652 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e36 y X0 y
               have i₂ := b7e1637
               grind)
            | exact superpose b7e1637 b7e36
            | exact resolve b7e36 b7e1637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e1658 : (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b7e1652 x
               have i₂ := b7e156 x
               grind)
            | exact superpose b7e156 b7e1652
            | exact resolve b7e1652 b7e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e156 b7e1652
          have b7e1665 : y = (M.op y x) := by
            first
            | (have i₁ := b7e1658
               have i₂ := b7e1637
               grind)
            | exact superpose b7e1637 b7e1658
            | exact resolve b7e1658 b7e1637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1637 b7e1658
          have b7e1669 : False := by grind
          exact b7e1669
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b8e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b8e1339 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e64 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e1340 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1339
               have r₂ := b8e24
               grind)
            | exact resolve b8e1339 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1339
          have b8e1341 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1340
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1340
            | exact resolve b8e1340 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1340
          have b8e1342 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1341
               grind)
            | exact superpose b8e1341 b8e20
            | exact resolve b8e20 b8e1341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1341
          have b8e1578 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e1342
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1342
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1342 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1342
          have b8e1579 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e1578
          have b8e1581 : y = (M.op y x) := by
            first
            | (have r₁ := b8e1579
               have r₂ := b8e21
               grind)
            | exact resolve b8e1579 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1579
          have b8e1583 : False := by grind
          exact b8e1583
