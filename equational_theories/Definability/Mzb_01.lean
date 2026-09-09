import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pyx_Equation3744 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
        intro X0 X1 X2 X3
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e36 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 x X1 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X2 (M.op X3 X1) X4 (M.op X0 x)
           have i₂ := b0e11 X0 X1 x X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e38 x X1 X2 X3 x
           have i₂ := b0e11 X2 X1 x x
           grind)
        | exact superpose b0e11 b0e38
        | exact resolve b0e38 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e97 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 y X2 (M.op X0 x)
           have i₂ := b0e36 X0 x
           grind)
        | exact superpose b0e36 b0e11
        | exact resolve b0e11 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e100 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
        intro X1
        first
        | (have i₁ := b0e97 x X1 x
           have i₂ := b0e11 X1 x x x
           grind)
        | exact superpose b0e11 b0e97
        | exact resolve b0e97 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97
      have b0e128 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e40 (σ x) X0 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e40
        | exact resolve b0e40 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e329 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e128 (σ x)
           grind)
        | exact superpose b0e128 b0e18
        | exact resolve b0e18 b0e128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128
      have b0e333 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e329
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e329
        | exact resolve b0e329 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e329
      have b0e345 : (σ y) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e333
           have i₂ := b0e100 x
           grind)
        | exact superpose b0e100 b0e333
        | exact resolve b0e333 b0e100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100 b0e333
      have b0e350 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e345
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e345
        | exact resolve b0e345 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e345
      have b0e351 : False := by grind
      exact b0e351
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
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
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
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
        have b1e32 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e12 X2 (M.op X3 X1) X4 (M.op X0 x)
             have i₂ := b1e12 X0 X1 x X3
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b1e32 x X1 X2 X3 x
             have i₂ := b1e12 X2 X1 x x
             grind)
          | exact superpose b1e12 b1e32
          | exact resolve b1e32 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b1e69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X1 X2 X1 X3
             have i₂ := b1e17 X1 X0
             grind)
          | (have i₁ := b1e12 X0 X1 X2 X3
             have i₂ := b1e17 X0 (M.op X0 X2)
             grind)
          | exact superpose b1e17 b1e12
          | (have j1 := b1e17 X1 X0
             grind)
          | exact resolve b1e12 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e69 X0 X1 X2 x
             have i₂ := b1e34 X2 X0 x
             grind)
          | exact superpose b1e34 b1e69
          | (have j0 := b1e69 X0 X1 X2 x
             grind)
          | exact resolve b1e69 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e69
        have b1e265 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b1e432 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e265
        have b1e445 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e432 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e432
          | exact resolve b1e432 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e432
        have b1e598 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e73 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e599 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e598 X0 X1
             have j1 := b1e17 X1 X0
             grind)
          | (have r₁ := b1e598 (k X0 X0) X0
             have r₂ := b1e17 X0 X0
             grind)
          | (have r₁ := b1e598 X1 X0
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e598 (M.op X0 X0) X1
             have r₂ := b1e17 X0 (M.op X1 X1)
             grind)
          | exact resolve b1e598 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e598
        have b1e1045 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e64 x x
             grind)
          | exact superpose b1e64 b1e21
          | (have j1 := b1e64 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e64 y x
             grind)
          | exact resolve b1e21 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e1110 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e1045
        have b1e1528 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1110
             have i₂ := b1e599 x x
             grind)
          | exact superpose b1e599 b1e1110
          | (have j1 := b1e599 (σ x) (σ x)
             grind)
          | exact resolve b1e1110 b1e599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1110
        have b1e1530 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1528
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1528
          | exact resolve b1e1528 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1528
        have b1e1531 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1530
        have b1e1535 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e1531
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1531
          | exact resolve b1e1531 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1531
        have b1e1549 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e445 x
             have i₂ := b1e1535
             grind)
          | exact superpose b1e1535 b1e445
          | exact resolve b1e445 b1e1535
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e445 b1e1535
        have b1e1571 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e1549
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1549
          | exact resolve b1e1549 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1549
        have b1e1737 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e599 x x
             have i₂ := b1e1571
             grind)
          | exact superpose b1e1571 b1e599
          | (have j0 := b1e599 x x
             grind)
          | exact resolve b1e599 b1e1571
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e599 b1e1571
        have b1e1738 : x = (M.op x x) ∨ x = y := by grind
        clear b1e1737
        have b1e1750 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e1738
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1738
          | exact resolve b1e1738 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1738
        have b1e1751 : x = y := by grind
        clear b1e1750
        have b1e1890 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e1751
             grind)
          | exact superpose b1e1751 b1e22
          | exact resolve b1e22 b1e1751
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2105 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1890
             grind)
          | exact superpose b1e1890 b1e21
          | exact resolve b1e21 b1e1890
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1890
        have b1e2133 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e2105
             have i₂ := b1e1751
             grind)
          | exact superpose b1e1751 b1e2105
          | exact resolve b1e2105 b1e1751
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1751 b1e2105
        have b1e2134 : False := by grind
        exact b1e2134
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
        have b2e31 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b2e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e307 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e64 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e308 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e307
             have r₂ := b2e22
             grind)
          | exact resolve b2e307 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e307
        have b2e309 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e308
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e308
          | exact resolve b2e308 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e308
        have b2e310 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e309
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e309
          | exact resolve b2e309 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e309
        have b2e311 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e310
             grind)
          | exact superpose b2e310 b2e22
          | exact resolve b2e22 b2e310
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e317 : (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b2e31 (σ y) (σ x)
             have i₂ := b2e310
             grind)
          | exact superpose b2e310 b2e31
          | exact resolve b2e31 b2e310
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e310
        have b2e319 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b2e317
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e317
          | exact resolve b2e317 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e317
        have b2e517 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e319
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e319
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e319 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e319
        have b2e523 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b2e517
        have b2e529 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e523
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e523
          | exact resolve b2e523 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e523
        have b2e531 : x = (M.op x x) := by
          first
          | (have r₁ := b2e529
             have r₂ := b2e311
             grind)
          | exact resolve b2e529 b2e311
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e529
        have b2e648 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e531
             grind)
          | exact superpose b2e531 b2e20
          | exact resolve b2e20 b2e531
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e531
        have b2e801 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e311
             have i₂ := b2e648
             grind)
          | exact superpose b2e648 b2e311
          | exact resolve b2e311 b2e648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e311 b2e648
        have b2e802 : False := by grind
        exact b2e802
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e40 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X1 X0)) := by
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
        have b3e43 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 x X1 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e12 X2 (M.op X3 X1) X4 (M.op X0 x)
             have i₂ := b3e12 X0 X1 x X3
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b3e47 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b3e45 x X1 X2 X3 x
             have i₂ := b3e12 X2 X1 x x
             grind)
          | exact superpose b3e12 b3e45
          | exact resolve b3e45 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e49 : y = (M.op y y) := by
          first
          | (have i₁ := b3e40 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e40
          | exact resolve b3e40 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b3e81 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X1 X2 X1 X3
             have i₂ := b3e17 X1 X0
             grind)
          | (have i₁ := b3e12 X0 X1 X2 X3
             have i₂ := b3e17 X0 (M.op X0 X2)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X1 X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e85 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e81 X0 X1 X2 x
             have i₂ := b3e47 X2 X0 x
             grind)
          | exact superpose b3e47 b3e81
          | (have j0 := b3e81 X0 X1 X2 x
             grind)
          | exact resolve b3e81 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e103 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 y X2 (M.op X0 x)
             have i₂ := b3e43 X0 x
             grind)
          | exact superpose b3e43 b3e12
          | exact resolve b3e12 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e106 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b3e103 x X1 x
             have i₂ := b3e12 X1 x x x
             grind)
          | exact superpose b3e12 b3e103
          | exact resolve b3e103 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e103
        have b3e131 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e47 (σ x) X0 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e47
          | exact resolve b3e47 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e324 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e131 (σ x)
             grind)
          | exact superpose b3e131 b3e19
          | exact resolve b3e19 b3e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e131
        have b3e345 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e324
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e324
          | exact resolve b3e324 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e324
        have b3e351 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e345
             have i₂ := b3e106 x
             grind)
          | exact superpose b3e106 b3e345
          | exact resolve b3e345 b3e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106 b3e345
        have b3e538 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e85 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e539 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e538 X0 X1
             have j1 := b3e17 X1 X0
             grind)
          | (have r₁ := b3e538 (k X0 X0) X0
             have r₂ := b3e17 X0 X0
             grind)
          | (have r₁ := b3e538 X1 X0
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e538 (M.op X0 X0) X1
             have r₂ := b3e17 X0 (M.op X1 X1)
             grind)
          | exact resolve b3e538 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e538
        have b3e970 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e73 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e73
          | exact resolve b3e73 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e1065 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e970
        have b3e1222 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e1065
             have i₂ := b3e539 x x
             grind)
          | exact superpose b3e539 b3e1065
          | (have j1 := b3e539 x x
             grind)
          | exact resolve b3e1065 b3e539
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e539
        have b3e1242 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e1222
             have r₂ := b3e351
             grind)
          | exact resolve b3e1222 b3e351
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e351 b3e1222
        have b3e1385 : x = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e46 x x
             have i₂ := b3e1242
             grind)
          | exact superpose b3e1242 b3e46
          | exact resolve b3e46 b3e1242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46 b3e1242
        have b3e1529 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1065
             have i₂ := b3e1385
             grind)
          | exact superpose b3e1385 b3e1065
          | exact resolve b3e1065 b3e1385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1065 b3e1385
        have b3e1538 : (σ x) = (σ y) := by grind
        clear b3e1529
        have b3e1584 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e1538
             grind)
          | exact superpose b3e1538 b3e13
          | exact resolve b3e13 b3e1538
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1616 : x = y := by
          first
          | (have i₁ := b3e1584
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1584
          | exact resolve b3e1584 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1584
        have b3e1661 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e1616
             grind)
          | exact superpose b3e1616 b3e19
          | exact resolve b3e19 b3e1616
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1669 : x = (M.op x x) := by
          first
          | (have i₁ := b3e49
             have i₂ := b3e1616
             grind)
          | exact superpose b3e1616 b3e49
          | exact resolve b3e49 b3e1616
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49 b3e1616
        have b3e1672 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1661
             have i₂ := b3e1669
             grind)
          | exact superpose b3e1669 b3e1661
          | exact resolve b3e1661 b3e1669
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1661 b3e1669
        have b3e1673 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e1672
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1672
          | exact resolve b3e1672 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1672
        have b3e1674 : False := by grind
        exact b3e1674
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
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
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b4e31 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 x X1 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e13 X2 (M.op X3 X1) X4 (M.op X0 x)
               have i₂ := b4e13 X0 X1 x X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b4e35 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e33 x X1 X2 X3 x
               have i₂ := b4e13 X2 X1 x x
               grind)
            | exact superpose b4e13 b4e33
            | exact resolve b4e33 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b4e62 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e66 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
          have b4e70 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e66 X0 X1 X2 x
               have i₂ := b4e35 X2 X0 x
               grind)
            | exact superpose b4e35 b4e66
            | (have j0 := b4e66 X0 X1 X2 x
               grind)
            | exact resolve b4e66 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e88 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 y X2 (M.op X0 x)
               have i₂ := b4e31 X0 x
               grind)
            | exact superpose b4e31 b4e13
            | exact resolve b4e13 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e91 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b4e88 x X1 x
               have i₂ := b4e13 X1 x x x
               grind)
            | exact superpose b4e13 b4e88
            | exact resolve b4e88 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88
          have b4e105 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e35 (σ x) X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e35
            | exact resolve b4e35 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e204 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b4e228 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e105 (σ x)
               grind)
            | exact superpose b4e105 b4e20
            | exact resolve b4e20 b4e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e246 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e228
               have i₂ := b4e91 x
               grind)
            | exact superpose b4e91 b4e228
            | exact resolve b4e228 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e228
          have b4e287 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e204 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e204
            | exact resolve b4e204 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e204
          have b4e394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e62 (σ X1) (σ X0)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e62
            | (have j0 := b4e62 (σ X1) (σ X0)
               grind)
            | exact resolve b4e62 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e516 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e70 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e517 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e516 X0 X1
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e516 (k X0 X0) X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e516 X1 X0
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e516 (M.op X0 X0) X1
               have r₂ := b4e18 X0 (M.op X1 X1)
               grind)
            | exact resolve b4e516 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e516
          have b4e715 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e26 X1 X0
               have i₂ := b4e517 X0 (τ X1)
               grind)
            | exact superpose b4e517 b4e26
            | (have j1 := b4e517 X0 (τ X1)
               grind)
            | exact resolve b4e26 b4e517
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e927 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e60 x x
               grind)
            | exact superpose b4e60 b4e23
            | (have j1 := b4e60 x x
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e60 y x
               grind)
            | exact resolve b4e23 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e984 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e60 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e986 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e984 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e984
          have b4e990 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e927
          have b4e1401 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e986 (M.op X0 X1)
               have i₂ := b4e34 X0 X1
               grind)
            | exact superpose b4e34 b4e986
            | (have j0 := b4e986 (M.op X0 X1)
               grind)
            | exact resolve b4e986 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1406 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e986 (τ X0)
               have i₂ := b4e27 X0 (τ X0)
               grind)
            | exact superpose b4e27 b4e986
            | (have j0 := b4e986 (τ X0)
               grind)
            | exact resolve b4e986 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e986
          have b4e1409 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b4e1401 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1401
          have b4e1411 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e1406 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1406
            | (have j0 := b4e1406 X0
               grind)
            | exact resolve b4e1406 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1406
          have b4e1415 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e1411 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1411
            | (have j0 := b4e1411 X0
               grind)
            | exact resolve b4e1411 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1411
          have b4e1423 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e990
               have i₂ := b4e517 x x
               grind)
            | exact superpose b4e517 b4e990
            | (have j1 := b4e517 (σ x) (σ x)
               grind)
            | exact resolve b4e990 b4e517
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e517 b4e990
          have b4e1432 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b4e1415 (τ X0)
               have i₂ := b4e287 X0 X0
               grind)
            | exact superpose b4e287 b4e1415
            | (have j0 := b4e1415 (τ X0)
               grind)
            | exact resolve b4e1415 b4e287
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287 b4e1415
          have b4e3511 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1432 (M.op X0 X1)
               have i₂ := b4e34 X0 X1
               grind)
            | exact superpose b4e34 b4e1432
            | (have j0 := b4e1432 (M.op X0 X1)
               grind)
            | exact resolve b4e1432 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e1432
          have b4e3525 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b4e3511 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3511
          have b4e5204 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e715 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e715
            | exact resolve b4e715 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e715
          have b4e5276 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e5204 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e5204
            | (have j0 := b4e5204 X0 X1
               grind)
            | exact resolve b4e5204 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5204
          have b4e5675 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e394 y x
               grind)
            | exact superpose b4e394 b4e20
            | (have j1 := b4e394 y x
               grind)
            | exact resolve b4e20 b4e394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e394
          have b4e5738 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e5675
               have i₂ := b4e91 x
               grind)
            | exact superpose b4e91 b4e5675
            | exact resolve b4e5675 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5675
          have b4e5747 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b4e5738
               have i₂ := b4e105 (σ x)
               grind)
            | exact superpose b4e105 b4e5738
            | exact resolve b4e5738 b4e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105 b4e5738
          have b4e64665 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e5747
               have i₂ := b4e5276 y x
               grind)
            | exact superpose b4e5276 b4e5747
            | (have j1 := b4e5276 (σ x) (σ x)
               grind)
            | exact resolve b4e5747 b4e5276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5276 b4e5747
          have b4e64671 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e64665
               have i₂ := b4e91 x
               grind)
            | exact superpose b4e91 b4e64665
            | exact resolve b4e64665 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64665
          have b4e64672 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
          clear b4e64671
          have b4e64693 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e64672
               have i₂ := b4e91 x
               grind)
            | exact superpose b4e91 b4e64672
            | exact resolve b4e64672 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64672
          have b4e64703 : x = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e64693
               have i₂ := b4e91 x
               grind)
            | exact superpose b4e91 b4e64693
            | exact resolve b4e64693 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91 b4e64693
          have b4e64713 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b4e64703
               have r₂ := b4e1423
               grind)
            | exact resolve b4e64703 b4e1423
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1423 b4e64703
          have b4e64812 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e3525 (σ x) (σ x)
               have i₂ := b4e64713
               grind)
            | exact superpose b4e64713 b4e3525
            | exact resolve b4e3525 b4e64713
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3525 b4e64713
          have b4e64828 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e64812
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e64812
            | exact resolve b4e64812 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64812
          have b4e64829 : x = (M.op x x) := by grind
          clear b4e64828
          have b4e65237 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e1409 x x
               have i₂ := b4e64829
               grind)
            | exact superpose b4e64829 b4e1409
            | exact resolve b4e1409 b4e64829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1409
          have b4e68047 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e246
               have i₂ := b4e65237
               grind)
            | exact superpose b4e65237 b4e246
            | exact resolve b4e246 b4e65237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e246 b4e65237
          have b4e68142 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e68047
               have i₂ := b4e64829
               grind)
            | exact superpose b4e64829 b4e68047
            | exact resolve b4e68047 b4e64829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64829 b4e68047
          have b4e68143 : False := by grind
          exact b4e68143
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
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
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b5e28 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X1 X0)) := by
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
          have b5e29 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b5e13 (M.op X0 X2) X3 (M.op x X1) X5
               have i₂ := b5e13 X0 X1 X2 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 x X1 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X2 (M.op X3 X1) X4 (M.op X0 x)
               have i₂ := b5e13 X0 X1 x X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b5e33 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b5e31 x X1 X2 X3 x
               have i₂ := b5e13 X2 X1 x x
               grind)
            | exact superpose b5e13 b5e31
            | exact resolve b5e31 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e34 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e29 X0 x X2 X3 x
               have i₂ := b5e13 X0 X3 x x
               grind)
            | exact superpose b5e13 b5e29
            | exact resolve b5e29 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e35 : y = (M.op y y) := by
            first
            | (have i₁ := b5e28 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e28
            | exact resolve b5e28 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e42 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e45 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e42
          have b5e48 : x = (k x y) := by
            first
            | (have r₁ := b5e45
               have r₂ := b5e21
               grind)
            | exact resolve b5e45 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e59 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X1 X3
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2 X3
               have i₂ := b5e18 X0 (M.op X0 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e63 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e59 X0 X1 X2 x
               have i₂ := b5e33 X2 X0 x
               grind)
            | exact superpose b5e33 b5e59
            | (have j0 := b5e59 X0 X1 X2 x
               grind)
            | exact resolve b5e59 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e68 : y = (k y y) := by grind
          clear b5e35
          have b5e80 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 y X2 (M.op X0 x)
               have i₂ := b5e30 X0 x
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e83 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b5e80 x X1 x
               have i₂ := b5e13 X1 x x x
               grind)
            | exact superpose b5e13 b5e80
            | exact resolve b5e80 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e180 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          have b5e184 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e14
            | exact resolve b5e14 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e185 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e180 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e180
            | exact resolve b5e180 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180
          have b5e192 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e195 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e184 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e184
            | exact resolve b5e184 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e242 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e55 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e270 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e61 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e271 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e270
               have r₂ := b5e24
               grind)
            | exact resolve b5e270 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e270
          have b5e272 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e271
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e271
            | exact resolve b5e271 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e271
          have b5e273 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e272
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e272
            | exact resolve b5e272 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e272
          have b5e274 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e273
               grind)
            | exact superpose b5e273 b5e24
            | exact resolve b5e24 b5e273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e279 : (σ x) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b5e32 (σ y) (σ x)
               have i₂ := b5e273
               grind)
            | exact superpose b5e273 b5e32
            | exact resolve b5e32 b5e273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e280 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e34 (σ y) (σ x) X0
               have i₂ := b5e273
               grind)
            | exact superpose b5e273 b5e34
            | exact resolve b5e34 b5e273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e281 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b5e279
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e279
            | exact resolve b5e279 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e279
          have b5e351 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e63 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e352 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e351 X0 X1
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e351 (k X0 X0) X0
               have r₂ := b5e18 X0 X0
               grind)
            | (have r₁ := b5e351 X1 X0
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e351 (M.op X0 X0) X1
               have r₂ := b5e18 X0 (M.op X1 X1)
               grind)
            | exact resolve b5e351 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e351
          have b5e472 : (k x x) = (τ (σ x)) := by
            first
            | (have i₁ := b5e14 (k x x)
               have i₂ := b5e281
               grind)
            | exact superpose b5e281 b5e14
            | exact resolve b5e14 b5e281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e281
          have b5e474 : x = (k x x) := by
            first
            | (have i₁ := b5e472
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e472
            | exact resolve b5e472 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e472
          have b5e519 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e474
               grind)
            | exact superpose b5e474 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e474
          have b5e520 : x = (M.op x x) := by grind
          clear b5e519
          have b5e580 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e520
               grind)
            | exact superpose b5e520 b5e21
            | exact resolve b5e21 b5e520
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e520
          have b5e670 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e53 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e672 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e670 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e670
          have b5e831 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e184 X1 X0
               have i₂ := b5e352 (σ X0) X1
               grind)
            | exact superpose b5e352 b5e184
            | (have j1 := b5e352 (σ X0) X1
               grind)
            | exact resolve b5e184 b5e352
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e832 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (M.op (τ X0) (τ X0))) X0) ∨ (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e185 X0
               have i₂ := b5e352 (σ (M.op (τ X0) (τ X0))) X0
               grind)
            | exact superpose b5e352 b5e185
            | (have j1 := b5e352 (σ (M.op (τ X0) (τ X0))) X0
               grind)
            | exact resolve b5e185 b5e352
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e836 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e352 (σ X0) (σ X1)
               grind)
            | exact superpose b5e352 b5e19
            | (have j1 := b5e352 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e352
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e837 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e192 X1 X0
               have i₂ := b5e352 X0 (σ X1)
               grind)
            | exact superpose b5e352 b5e192
            | (have j1 := b5e352 X0 (σ X1)
               grind)
            | exact resolve b5e192 b5e352
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e192
          have b5e1230 : ∀ X0 X1 : G, y ≠ (M.op X0 x) ∨ y = (k y (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b5e242 y (M.op X0 X1)
               have i₂ := b5e30 X0 X1
               grind)
            | exact superpose b5e30 b5e242
            | (have j0 := b5e242 y (M.op X0 X1)
               grind)
            | exact resolve b5e242 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e1307 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e672 (τ X0)
               have i₂ := b5e27 X0 (τ X0)
               grind)
            | exact superpose b5e27 b5e672
            | (have j0 := b5e672 (τ X0)
               grind)
            | exact resolve b5e672 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e672
          have b5e1315 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e1307 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1307
            | (have j0 := b5e1307 X0
               grind)
            | exact resolve b5e1307 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1307
          have b5e1319 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1315 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1315
            | (have j0 := b5e1315 X0
               grind)
            | exact resolve b5e1315 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1315
          have b5e1546 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e1319 (τ X0)
               have i₂ := b5e195 X0 X0
               grind)
            | exact superpose b5e195 b5e1319
            | (have j0 := b5e1319 (τ X0)
               grind)
            | exact resolve b5e1319 b5e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1319
          have b5e4321 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e1546 (M.op X0 X1)
               have i₂ := b5e32 X0 X1
               grind)
            | exact superpose b5e32 b5e1546
            | (have j0 := b5e1546 (M.op X0 X1)
               grind)
            | exact resolve b5e1546 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e1546
          have b5e4336 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b5e4321 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4321
          have b5e6997 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e837 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e837
            | exact resolve b5e837 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e837
          have b5e7069 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e6997 X0 X1
               have i₂ := b5e195 X1 X0
               grind)
            | exact superpose b5e195 b5e6997
            | (have j0 := b5e6997 X0 X1
               grind)
            | exact resolve b5e6997 b5e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6997
          have b5e7522 : ∀ X0 X1 : G, (k X1 X0) = (k (k X1 X0) (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e185 (k X0 X1)
               have i₂ := b5e7069 X0 X1
               grind)
            | exact superpose b5e7069 b5e185
            | (have j1 := b5e7069 X1 X0
               grind)
            | exact resolve b5e185 b5e7069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e185
          have b5e7526 : ∀ X0 X1 X2 : G, (τ (k (k X1 X0) X2)) = (k (τ (M.op X0 X1)) (τ X2)) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e195 X2 (k X1 X0)
               have i₂ := b5e7069 X1 X0
               grind)
            | exact superpose b5e7069 b5e195
            | (have j1 := b5e7069 X1 X0
               grind)
            | exact resolve b5e195 b5e7069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7069
          have b5e7539 : ∀ X0 X1 X2 : G, (τ (k (k X1 X0) X2)) = (τ (k (M.op X0 X1) X2)) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e7526 X0 X1 X2
               have i₂ := b5e195 X2 (M.op X0 X1)
               grind)
            | exact superpose b5e195 b5e7526
            | (have j0 := b5e7526 X0 X1 X2
               grind)
            | exact resolve b5e7526 b5e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7526
          have b5e7541 : ∀ X0 X1 : G, (k X1 X0) = (k (k X1 X0) (σ (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e7522 X0 X1
               have i₂ := b5e4336 X0 X1
               grind)
            | exact superpose b5e4336 b5e7522
            | (have j0 := b5e7522 X0 X1
               grind)
            | exact resolve b5e7522 b5e4336
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4336 b5e7522
          have b5e7558 : ∀ X0 X1 : G, (k X1 X0) = (k (k X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e7541 X0 X1
               have i₂ := b5e15 (M.op X0 X1)
               grind)
            | exact superpose b5e15 b5e7541
            | (have j0 := b5e7541 X0 X1
               grind)
            | exact resolve b5e7541 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7541
          have b5e11365 : ∀ X0 : G, (k (τ y) X0) = (τ (M.op (σ X0) x)) ∨ (σ X0) = (M.op (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b5e831 X0 y
               have i₂ := b5e83 (σ X0)
               grind)
            | exact superpose b5e83 b5e831
            | (have j0 := b5e831 X0 x
               grind)
            | exact resolve b5e831 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e17192 : ∀ X0 : G, (k (τ y) X0) = (k (τ x) X0) ∨ (σ X0) = (M.op (σ X0) x) ∨ (σ X0) = (M.op (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b5e831 X0 x
               have i₂ := b5e11365 X0
               grind)
            | exact superpose b5e11365 b5e831
            | (have j0 := b5e831 X0 x
               have j1 := b5e11365 X0
               grind)
            | exact resolve b5e831 b5e11365
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11365
          have b5e17220 : ∀ X0 : G, (k (τ y) X0) = (k (τ x) X0) ∨ (σ X0) = (M.op (σ X0) x) := by
            intro X0
            first
            | (have j0 := b5e17192 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17192
          have b5e19915 : ∀ X0 : G, (k (σ (τ y)) X0) = (σ (k (τ x) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 (τ y)
               have i₂ := b5e17220 (τ X0)
               grind)
            | exact superpose b5e17220 b5e27
            | (have j1 := b5e17220 (τ X0)
               grind)
            | exact resolve b5e27 b5e17220
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17220
          have b5e19939 : ∀ X0 : G, (k (σ (τ y)) X0) = (k (σ (τ x)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b5e19915 X0
               have i₂ := b5e27 X0 (τ x)
               grind)
            | exact superpose b5e27 b5e19915
            | (have j0 := b5e19915 X0
               grind)
            | exact resolve b5e19915 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e19915
          have b5e19980 : ∀ X0 : G, (k x X0) = (k (σ (τ y)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b5e19939 X0
               have i₂ := b5e15 x
               grind)
            | exact superpose b5e15 b5e19939
            | (have j0 := b5e19939 X0
               grind)
            | exact resolve b5e19939 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19939
          have b5e20011 : ∀ X0 : G, (k x X0) = (k y X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b5e19980 X0
               have i₂ := b5e15 y
               grind)
            | exact superpose b5e15 b5e19980
            | (have j0 := b5e19980 X0
               grind)
            | exact resolve b5e19980 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19980
          have b5e20040 : ∀ X0 : G, (k x X0) = (k y X0) ∨ (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e20011 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e20011
            | (have j0 := b5e20011 X0
               grind)
            | exact resolve b5e20011 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20011
          have b5e27923 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e836 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e836
          have b5e28272 : ∀ X0 : G, y ≠ y ∨ y = (k y (M.op y X0)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e1230 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1230
            | (have j0 := b5e1230 y X0
               grind)
            | (have r₁ := b5e1230 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e1230 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1230
          have b5e28273 : ∀ X0 : G, y = (k y (M.op y X0)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b5e28272 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28272
          have b5e28319 : ∀ X0 : G, y = (k x (M.op y X0)) ∨ (M.op y X0) = (M.op (M.op y X0) x) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e20040 (M.op y X0)
               have i₂ := b5e28273 X0
               grind)
            | exact superpose b5e28273 b5e20040
            | (have j0 := b5e20040 (M.op y X0)
               have j1 := b5e28273 X0
               grind)
            | exact resolve b5e20040 b5e28273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20040 b5e28273
          have b5e28364 : ∀ X0 : G, (M.op y x) = (M.op y X0) ∨ y = (k x (M.op y X0)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e28319 X0
               have i₂ := b5e34 y X0 x
               grind)
            | exact superpose b5e34 b5e28319
            | (have j0 := b5e28319 X0
               grind)
            | exact resolve b5e28319 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28319
          have b5e28385 : ∀ X0 : G, y = (M.op y X0) ∨ y = (k x (M.op y X0)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e28364 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e28364
            | (have j0 := b5e28364 X0
               grind)
            | exact resolve b5e28364 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28364
          have b5e28386 : ∀ X0 : G, y = (k x (M.op y X0)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b5e28385 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28385
          have b5e30451 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e27923 (τ X1) (τ X0)
               have i₂ := b5e195 X1 X0
               grind)
            | exact superpose b5e195 b5e27923
            | (have j0 := b5e27923 (τ X1) (τ X0)
               grind)
            | exact resolve b5e27923 b5e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e195 b5e27923
          have b5e30525 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e30451 X0 X1
               have i₂ := b5e15 (k X0 X1)
               grind)
            | exact superpose b5e15 b5e30451
            | (have j0 := b5e30451 X0 X1
               grind)
            | exact resolve b5e30451 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30451
          have b5e30534 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e30525 X0 X1
               have i₂ := b5e15 X1
               grind)
            | exact superpose b5e15 b5e30525
            | (have j0 := b5e30525 X0 X1
               grind)
            | exact resolve b5e30525 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30525
          have b5e30540 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e30534 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e30534
            | (have j0 := b5e30534 X0 X1
               grind)
            | exact resolve b5e30534 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30534
          have b5e30541 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e30540 X0 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e30540
            | (have j0 := b5e30540 X0 X1
               grind)
            | exact resolve b5e30540 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30540
          have b5e30719 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (k X0 X1)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e30541 (k X0 X1) (M.op X1 X0)
               have i₂ := b5e7558 X1 X0
               grind)
            | exact superpose b5e7558 b5e30541
            | (have j0 := b5e30541 (k X0 X1) (M.op X1 X0)
               have j1 := b5e7558 (M.op X1 X0) (k X0 X1)
               grind)
            | exact resolve b5e30541 b5e7558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7558 b5e30541
          have b5e30764 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (k X0 X1)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e30719 X0 X1
               have j1 := b5e352 (M.op X1 X0) (k X0 X1)
               grind)
            | (have r₁ := b5e30719 X1 X0
               have r₂ := b5e352 X0 X1
               grind)
            | exact resolve b5e30719 b5e352
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30719
          have b5e30767 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X1)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e30764 X0 X1
               have i₂ := b5e34 X1 X0 (k X0 X1)
               grind)
            | exact superpose b5e34 b5e30764
            | (have j0 := b5e30764 X0 X1
               grind)
            | exact resolve b5e30764 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e30764
          have b5e32509 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (k X1 X0)) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 (k X1 X0) X2 X0
               have i₂ := b5e30767 X1 X0
               grind)
            | exact superpose b5e30767 b5e33
            | (have j1 := b5e30767 X1 X0
               grind)
            | exact resolve b5e33 b5e30767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32522 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (k X1 X0) = (k (k X1 X0) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e242 (k X0 X1) X1
               have i₂ := b5e30767 X0 X1
               grind)
            | exact superpose b5e30767 b5e242
            | (have j0 := b5e242 (k X1 X0) X0
               have j1 := b5e30767 X1 X0
               grind)
            | (have r₁ := b5e242 X1 X1
               have r₂ := b5e30767 X1 X1
               grind)
            | exact resolve b5e242 b5e30767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e242 b5e30767
          have b5e32578 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (k X1 X0) = (k (k X1 X0) X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e32522 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32522
          have b5e32611 : ∀ X0 X1 : G, (k X1 X0) = (k (k X1 X0) X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e32578 X0 X1
               have j1 := b5e352 X0 X1
               grind)
            | (have r₁ := b5e32578 X0 X1
               have r₂ := b5e352 X0 X1
               grind)
            | exact resolve b5e32578 b5e352
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e352 b5e32578
          have b5e32612 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k X1 X0)) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e32509 X0 X1 X2
               have i₂ := b5e33 X1 X2 X0
               grind)
            | exact superpose b5e33 b5e32509
            | (have j0 := b5e32509 X0 X1 X2
               grind)
            | exact resolve b5e32509 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32509
          have b5e70914 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e832 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e832
          have b5e124114 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e70914 (σ X0)
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e70914
            | exact resolve b5e70914 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70914
          have b5e130665 : ∀ X0 X1 X2 : G, (k (k X1 X0) X2) = (σ (τ (k (M.op X0 X1) X2))) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e15 (k (k X1 X0) X2)
               have i₂ := b5e7539 X0 X1 X2
               grind)
            | exact superpose b5e7539 b5e15
            | (have j1 := b5e7539 X0 X1 X2
               grind)
            | exact resolve b5e15 b5e7539
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7539
          have b5e130685 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = (k (k X1 X0) X2) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e130665 X0 X1 X2
               have i₂ := b5e15 (k (M.op X0 X1) X2)
               grind)
            | exact superpose b5e15 b5e130665
            | (have j0 := b5e130665 X0 X1 X2
               grind)
            | exact resolve b5e130665 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e130665
          have b5e131311 : ∀ X0 X1 : G, (k X1 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e32611 X0 X1
               have i₂ := b5e130685 X0 X1 X0
               grind)
            | exact superpose b5e130685 b5e32611
            | (have j0 := b5e32611 X0 X1
               have j1 := b5e130685 X0 X1 x
               grind)
            | exact resolve b5e32611 b5e130685
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32611 b5e130685
          have b5e131420 : ∀ X0 X1 : G, (k X1 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e131311 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131311
          have b5e131996 : ∀ X0 X1 X2 : G, (k (M.op X2 X1) X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e131420 X2 (M.op x X1)
               have i₂ := b5e33 X1 X2 x
               grind)
            | exact superpose b5e33 b5e131420
            | (have j0 := b5e131420 X0 X1
               grind)
            | exact resolve b5e131420 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131420
          have b5e138863 : ∀ X0 : G, (k (σ x) (σ y)) = (k (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e131996 (σ y) (σ x) x
               have i₂ := b5e273
               grind)
            | exact superpose b5e273 b5e131996
            | exact resolve b5e131996 b5e273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e273
          have b5e138958 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X1)) = (M.op X3 (k (M.op X0 X1) X2)) ∨ (M.op X2 (M.op X2 X1)) = X2 ∨ (M.op X2 X1) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e32612 X2 (M.op X2 X1) X3
               have i₂ := b5e131996 X2 X1 X0
               grind)
            | (have i₁ := b5e32612 X0 (M.op X2 X1) X2
               have i₂ := b5e131996 X0 X1 X2
               grind)
            | exact superpose b5e131996 b5e32612
            | (have j0 := b5e32612 X2 (M.op X2 X1) X2
               have j1 := b5e131996 X2 (M.op X2 X1) X2
               grind)
            | exact resolve b5e32612 b5e131996
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32612 b5e131996
          have b5e139035 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op X3 (k (M.op X0 X1) X2)) ∨ (M.op X2 (M.op X2 X1)) = X2 ∨ (M.op X2 X1) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e138958 X0 X1 X2 X3
               have i₂ := b5e33 X1 X3 X2
               grind)
            | exact superpose b5e33 b5e138958
            | (have j0 := b5e138958 X0 X1 X2 X3
               grind)
            | exact resolve b5e138958 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e138958
          have b5e139081 : ∀ X0 : G, (k (σ x) (σ y)) = (k (M.op X0 (σ x)) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e138863 X0
               grind)
            | (have r₁ := b5e138863 X0
               have r₂ := b5e274
               grind)
            | exact resolve b5e138863 b5e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e274 b5e138863
          have b5e139099 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = X2 ∨ (M.op X3 X1) = (M.op X3 (k (M.op X0 X1) X2)) ∨ (M.op X2 X1) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e139035 X0 X1 X2 X3
               have i₂ := b5e33 X1 X2 X2
               grind)
            | exact superpose b5e33 b5e139035
            | (have j0 := b5e139035 X0 X1 X2 X3
               grind)
            | exact resolve b5e139035 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e139035
          have b5e139100 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op X3 (k (M.op X0 X1) X2)) ∨ (M.op X2 X1) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b5e139099 X0 X1 X2 X3
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e139099
          have b5e139120 : ∀ X0 : G, (σ (k x y)) = (k (M.op X0 (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e139081 X0
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e139081
            | exact resolve b5e139081 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e139081
          have b5e139134 : ∀ X0 : G, (σ x) = (k (M.op X0 (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e139120 X0
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e139120
            | exact resolve b5e139120 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e139120
          have b5e139661 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op X0 (σ x))) y) := by
            intro X0
            first
            | (have i₁ := b5e184 (M.op X0 (σ x)) y
               have i₂ := b5e139134 X0
               grind)
            | exact superpose b5e139134 b5e184
            | exact resolve b5e184 b5e139134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e184 b5e139134
          have b5e139707 : ∀ X0 : G, x = (k (τ (M.op X0 (σ x))) y) := by
            intro X0
            first
            | (have i₁ := b5e139661 X0
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e139661
            | exact resolve b5e139661 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e139661
          have b5e140718 : ∀ X0 : G, x = (k (k (τ (σ x)) X0) y) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e139707 (σ X0)
               have i₂ := b5e831 X0 (σ x)
               grind)
            | exact superpose b5e831 b5e139707
            | (have j1 := b5e831 X0 (σ x)
               grind)
            | exact resolve b5e139707 b5e831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e831
          have b5e140799 : ∀ X0 : G, x = (k (k x X0) y) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e140718 X0
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e140718
            | (have j0 := b5e140718 X0
               grind)
            | exact resolve b5e140718 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e140718
          have b5e150445 : ∀ X0 : G, x = (k y y) ∨ (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ x)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e140799 (M.op y X0)
               have i₂ := b5e28386 X0
               grind)
            | exact superpose b5e28386 b5e140799
            | (have j0 := b5e140799 (M.op y X0)
               have j1 := b5e28386 X0
               grind)
            | exact resolve b5e140799 b5e28386
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28386 b5e140799
          have b5e150532 : ∀ X0 : G, x = y ∨ (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ x)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e150445 X0
               have i₂ := b5e68
               grind)
            | exact superpose b5e68 b5e150445
            | (have j0 := b5e150445 X0
               grind)
            | exact resolve b5e150445 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68 b5e150445
          have b5e150534 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ x)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b5e150532 X0
               grind)
            | (have r₁ := b5e150532 X0
               have r₂ := b5e580
               grind)
            | exact resolve b5e150532 b5e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e580 b5e150532
          have b5e181937 : ∀ X0 : G, x = (k (τ (σ (M.op y X0))) y) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e139707 (σ (M.op y X0))
               have i₂ := b5e150534 X0
               grind)
            | exact superpose b5e150534 b5e139707
            | (have j1 := b5e150534 X0
               grind)
            | exact resolve b5e139707 b5e150534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e139707 b5e150534
          have b5e181976 : ∀ X0 : G, x = (k (M.op y X0) y) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e181937 X0
               have i₂ := b5e14 (M.op y X0)
               grind)
            | exact superpose b5e14 b5e181937
            | (have j0 := b5e181937 X0
               grind)
            | exact resolve b5e181937 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e181937
          have b5e182249 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 x) ∨ y = (M.op y X1) ∨ y = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e139100 y X1 y X0
               have i₂ := b5e181976 X1
               grind)
            | exact superpose b5e181976 b5e139100
            | (have j0 := b5e139100 X0 X1 y x
               have j1 := b5e181976 X1
               grind)
            | exact resolve b5e139100 b5e181976
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e139100 b5e181976
          have b5e182295 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 x) ∨ y = (M.op y X1) := by
            intro X0 X1
            first
            | (have j0 := b5e182249 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e182249
          have b5e185982 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e182295 y X0
               grind)
            | (have i₁ := b5e22
               have i₂ := b5e182295 y x
               grind)
            | exact superpose b5e182295 b5e22
            | (have j1 := b5e182295 X0 X0
               grind)
            | exact resolve b5e22 b5e182295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e182295
          have b5e186213 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b5e185982 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e185982
          have b5e187829 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e124114 y
               have i₂ := b5e186213 y
               grind)
            | exact superpose b5e186213 b5e124114
            | exact resolve b5e124114 b5e186213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e124114
          have b5e187836 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X1 X0 y
               have i₂ := b5e186213 X1
               grind)
            | exact superpose b5e186213 b5e33
            | exact resolve b5e33 b5e186213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e186213
          have b5e187998 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e187829
          have b5e188017 : (σ y) = (M.op (σ y) y) := by
            first
            | (have i₁ := b5e187998
               have i₂ := b5e187836 (σ y) (σ y)
               grind)
            | exact superpose b5e187836 b5e187998
            | exact resolve b5e187998 b5e187836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e187998
          have b5e188025 : (σ y) = (M.op (σ y) x) := by
            first
            | (have i₁ := b5e188017
               have i₂ := b5e83 (σ y)
               grind)
            | exact superpose b5e83 b5e188017
            | exact resolve b5e188017 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e188017
          have b5e188032 : (σ y) = (M.op (σ x) x) := by
            first
            | (have i₁ := b5e188025
               have i₂ := b5e280 x
               grind)
            | exact superpose b5e280 b5e188025
            | exact resolve b5e188025 b5e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e280 b5e188025
          have b5e196345 : (σ y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e187836 (σ x) (σ x)
               grind)
            | exact superpose b5e187836 b5e23
            | exact resolve b5e23 b5e187836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e187836
          have b5e196744 : (σ y) ≠ (M.op (σ x) x) := by
            first
            | (have i₁ := b5e196345
               have i₂ := b5e83 (σ x)
               grind)
            | exact superpose b5e83 b5e196345
            | exact resolve b5e196345 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83 b5e196345
          have b5e196997 : False := by grind
          exact b5e196997
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
        have b6e44 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b6e90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b6e92 : x = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e110 : x = (M.op y x) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e92
             have r₂ := b6e20
             grind)
          | exact resolve b6e92 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e119 : x = (M.op y x) := by
          first
          | (have r₁ := b6e110
             have r₂ := b6e21
             grind)
          | exact resolve b6e110 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e110
        have b6e128 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e119
             grind)
          | exact superpose b6e119 b6e21
          | exact resolve b6e21 b6e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e232 : x = (k x x) := by
          first
          | (have i₁ := b6e44 y x
             have i₂ := b6e119
             grind)
          | exact superpose b6e119 b6e44
          | exact resolve b6e44 b6e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44 b6e119
        have b6e393 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e90 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e90
          | exact resolve b6e90 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e455 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e393
        have b6e479 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e455
             have i₂ := b6e232
             grind)
          | exact superpose b6e232 b6e455
          | exact resolve b6e455 b6e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e232 b6e455
        have b6e480 : (σ x) = (σ y) := by grind
        clear b6e479
        have b6e524 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e480
             grind)
          | exact superpose b6e480 b6e13
          | exact resolve b6e13 b6e480
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e480
        have b6e534 : x = y := by
          first
          | (have i₁ := b6e524
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e524
          | exact resolve b6e524 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e524
        have b6e538 : False := by grind
        exact b6e538
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
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
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b7e29 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b7e13 (M.op X0 X2) X3 (M.op x X1) X5
               have i₂ := b7e13 X0 X1 X2 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e13 X2 (M.op X3 X1) X4 (M.op X0 x)
               have i₂ := b7e13 X0 X1 x X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b7e33 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b7e31 x X1 X2 X3 x
               have i₂ := b7e13 X2 X1 x x
               grind)
            | exact superpose b7e13 b7e31
            | exact resolve b7e31 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e34 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e29 X0 x X2 X3 x
               have i₂ := b7e13 X0 X3 x x
               grind)
            | exact superpose b7e13 b7e29
            | exact resolve b7e29 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e47 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e50 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e47
          have b7e53 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e23
               grind)
            | exact resolve b7e50 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e54 : (σ x) = (σ (k x y)) := by
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
          have b7e57 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e14
            | exact resolve b7e14 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e58 : x = (k x y) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e57
            | exact resolve b7e57 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b7e67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e71 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X2 X1 X3
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e13 X0 X1 X2 X3
               have i₂ := b7e18 X0 (M.op X0 X2)
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X1 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e77 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e71 X0 X1 X2 x
               have i₂ := b7e33 X2 X0 x
               grind)
            | exact superpose b7e33 b7e71
            | (have j0 := b7e71 X0 X1 X2 x
               grind)
            | exact resolve b7e71 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e90 : x = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e91 : x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e90
               have r₂ := b7e21
               grind)
            | exact resolve b7e90 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e93 : x = (M.op y x) := by
            first
            | (have r₁ := b7e91
               have r₂ := b7e22
               grind)
            | exact resolve b7e91 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e104 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (M.op X1 X1) ∨ (k X1 (M.op X0 X2)) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 X1 (M.op X0 X2)
               have i₂ := b7e34 X0 X2 X1
               grind)
            | exact superpose b7e34 b7e17
            | (have j0 := b7e17 X1 (M.op X0 X2)
               grind)
            | (have r₁ := b7e17 x (M.op X0 x)
               have r₂ := b7e34 X0 x x
               grind)
            | exact resolve b7e17 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e122 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e22
            | exact resolve b7e22 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e123 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e34 y x X0
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e34
            | exact resolve b7e34 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e129 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          have b7e133 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e26 X0 X1
               grind)
            | exact superpose b7e26 b7e14
            | exact resolve b7e14 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e134 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e129 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e129
            | exact resolve b7e129 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e129
          have b7e139 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e19 X2 (k X0 (τ X1))
               have i₂ := b7e27 X1 X0
               grind)
            | exact superpose b7e27 b7e19
            | exact resolve b7e19 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e141 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b7e178 : x = (M.op x x) := by
            first
            | (have i₁ := b7e93
               have i₂ := b7e123 x
               grind)
            | exact superpose b7e123 b7e93
            | exact resolve b7e93 b7e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e123
          have b7e216 : x = (k x x) := by grind
          clear b7e178
          have b7e225 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e32 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e234 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e225
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e225
            | exact resolve b7e225 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e225
          have b7e248 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e67 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e257 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e234
               grind)
            | exact superpose b7e234 b7e14
            | exact resolve b7e14 b7e234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e234
          have b7e259 : y = (k y y) := by
            first
            | (have i₁ := b7e257
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e257
            | exact resolve b7e257 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e257
          have b7e331 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e23
               have i₂ := b7e77 X0 (σ x) (σ x)
               grind)
            | (have i₁ := b7e23
               have i₂ := b7e77 (σ x) x (σ x)
               grind)
            | exact superpose b7e77 b7e23
            | (have j1 := b7e77 X0 (σ x) x
               grind)
            | exact resolve b7e23 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e341 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e77 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e342 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e341 X0 X1
               have j1 := b7e18 X1 X0
               grind)
            | (have r₁ := b7e341 (k X0 X0) X0
               have r₂ := b7e18 X0 X0
               grind)
            | (have r₁ := b7e341 X1 X0
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e341 (M.op X0 X0) X1
               have r₂ := b7e18 X0 (M.op X1 X1)
               grind)
            | exact resolve b7e341 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e341
          have b7e600 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e65 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e602 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e600 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e600
          have b7e673 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e133 X1 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e133
            | exact resolve b7e133 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e133
          have b7e845 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 X0
               have i₂ := b7e342 (σ X0) (σ X1)
               grind)
            | exact superpose b7e342 b7e19
            | (have j1 := b7e342 (σ X0) (σ X1)
               grind)
            | exact resolve b7e19 b7e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e846 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e141 X1 X0
               have i₂ := b7e342 X0 (σ X1)
               grind)
            | exact superpose b7e342 b7e141
            | (have j1 := b7e342 X0 (σ X1)
               grind)
            | exact resolve b7e141 b7e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141
          have b7e1140 : ∀ X0 X1 X2 : G, (σ (k X2 (k X1 (τ X0)))) = (k (σ X2) (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e139 X1 X0 X2
               have i₂ := b7e342 X0 (σ X1)
               grind)
            | exact superpose b7e342 b7e139
            | (have j1 := b7e342 X0 (σ X1)
               grind)
            | exact resolve b7e139 b7e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e139
          have b7e1308 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e602 (M.op X0 X1)
               have i₂ := b7e32 X0 X1
               grind)
            | exact superpose b7e32 b7e602
            | (have j0 := b7e602 (M.op X0 X1)
               grind)
            | exact resolve b7e602 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1311 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e602 x
               have i₂ := b7e216
               grind)
            | exact superpose b7e216 b7e602
            | (have j0 := b7e602 x
               grind)
            | exact resolve b7e602 b7e216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1314 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e602 (τ X0)
               have i₂ := b7e26 X0 (τ X0)
               grind)
            | exact superpose b7e26 b7e602
            | (have j0 := b7e602 (τ X0)
               grind)
            | exact resolve b7e602 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e602
          have b7e1319 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b7e1311
          have b7e1320 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b7e1308 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1308
          have b7e1323 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e1314 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e1314
            | (have j0 := b7e1314 X0
               grind)
            | exact resolve b7e1314 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1314
          have b7e1327 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1323 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e1323
            | (have j0 := b7e1323 X0
               grind)
            | exact resolve b7e1323 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1323
          have b7e1336 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e1319
               grind)
            | exact superpose b7e1319 b7e23
            | exact resolve b7e23 b7e1319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1319
          have b7e1507 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b7e1327 (τ X0)
               have i₂ := b7e673 X0 X0
               grind)
            | exact superpose b7e673 b7e1327
            | (have j0 := b7e1327 (τ X0)
               grind)
            | exact resolve b7e1327 b7e673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1327
          have b7e2192 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e104 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104
          have b7e2593 : ∀ X0 X1 : G, (σ y) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e331 (M.op X0 x)
               have i₂ := b7e34 X0 x (σ x)
               grind)
            | exact superpose b7e34 b7e331
            | (have j0 := b7e331 X0
               grind)
            | exact resolve b7e331 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e331
          have b7e4256 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1507 (M.op X0 X1)
               have i₂ := b7e32 X0 X1
               grind)
            | exact superpose b7e32 b7e1507
            | (have j0 := b7e1507 (M.op X0 X1)
               grind)
            | exact resolve b7e1507 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e1507
          have b7e4273 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b7e4256 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4256
          have b7e7586 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e846 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e846
            | exact resolve b7e846 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e846
          have b7e7660 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e7586 X0 X1
               have i₂ := b7e673 X1 X0
               grind)
            | exact superpose b7e673 b7e7586
            | (have j0 := b7e7586 X0 X1
               grind)
            | exact resolve b7e7586 b7e673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7586
          have b7e8182 : ∀ X0 X1 : G, (k X1 X0) = (k (k X1 X0) (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e134 (k X0 X1)
               have i₂ := b7e7660 X0 X1
               grind)
            | exact superpose b7e7660 b7e134
            | (have j1 := b7e7660 X1 X0
               grind)
            | exact resolve b7e134 b7e7660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e134
          have b7e8192 : ∀ X0 X1 X2 : G, (τ (k (k X1 X0) X2)) = (k (τ (M.op X0 X1)) (τ X2)) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e673 X2 (k X1 X0)
               have i₂ := b7e7660 X1 X0
               grind)
            | exact superpose b7e7660 b7e673
            | (have j1 := b7e7660 X1 X0
               grind)
            | exact resolve b7e673 b7e7660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7660
          have b7e8195 : ∀ X0 X1 X2 : G, (τ (k (k X1 X0) X2)) = (τ (k (M.op X0 X1) X2)) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e8192 X0 X1 X2
               have i₂ := b7e673 X2 (M.op X0 X1)
               grind)
            | exact superpose b7e673 b7e8192
            | (have j0 := b7e8192 X0 X1 X2
               grind)
            | exact resolve b7e8192 b7e673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8192
          have b7e8197 : ∀ X0 X1 : G, (k X1 X0) = (k (k X1 X0) (σ (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e8182 X0 X1
               have i₂ := b7e4273 X0 X1
               grind)
            | exact superpose b7e4273 b7e8182
            | (have j0 := b7e8182 X0 X1
               grind)
            | exact resolve b7e8182 b7e4273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4273 b7e8182
          have b7e8214 : ∀ X0 X1 : G, (k X1 X0) = (k (k X1 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e8197 X0 X1
               have i₂ := b7e15 (M.op X0 X1)
               grind)
            | exact superpose b7e15 b7e8197
            | (have j0 := b7e8197 X0 X1
               grind)
            | exact resolve b7e8197 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8197
          have b7e29815 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e845 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e845
          have b7e29949 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e29815 (τ X1) (τ X0)
               have i₂ := b7e673 X1 X0
               grind)
            | exact superpose b7e673 b7e29815
            | (have j0 := b7e29815 (τ X1) (τ X0)
               grind)
            | exact resolve b7e29815 b7e673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e673 b7e29815
          have b7e30039 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e29949 X0 X1
               have i₂ := b7e15 (k X0 X1)
               grind)
            | exact superpose b7e15 b7e29949
            | (have j0 := b7e29949 X0 X1
               grind)
            | exact resolve b7e29949 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29949
          have b7e30050 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e30039 X0 X1
               have i₂ := b7e15 X1
               grind)
            | exact superpose b7e15 b7e30039
            | (have j0 := b7e30039 X0 X1
               grind)
            | exact resolve b7e30039 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30039
          have b7e30057 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e30050 X0 X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e30050
            | (have j0 := b7e30050 X0 X1
               grind)
            | exact resolve b7e30050 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30050
          have b7e30060 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e30057 X0 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e30057
            | (have j0 := b7e30057 X0 X1
               grind)
            | exact resolve b7e30057 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30057
          have b7e38490 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (k X0 X1)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e30060 (k X0 X1) (M.op X1 X0)
               have i₂ := b7e8214 X1 X0
               grind)
            | exact superpose b7e8214 b7e30060
            | (have j0 := b7e30060 (k X0 X1) (M.op X1 X0)
               have j1 := b7e8214 (M.op X1 X0) (k X0 X1)
               grind)
            | exact resolve b7e30060 b7e8214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8214 b7e30060
          have b7e38512 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (k X0 X1)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e38490 X0 X1
               have j1 := b7e342 (M.op X1 X0) (k X0 X1)
               grind)
            | (have r₁ := b7e38490 X1 X0
               have r₂ := b7e342 X0 X1
               grind)
            | exact resolve b7e38490 b7e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38490
          have b7e38567 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X1)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e38512 X0 X1
               have i₂ := b7e34 X1 X0 (k X0 X1)
               grind)
            | exact superpose b7e34 b7e38512
            | (have j0 := b7e38512 X0 X1
               grind)
            | exact resolve b7e38512 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38512
          have b7e39334 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (k X1 X0) = (k (k X1 X0) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e248 (k X0 X1) X1
               have i₂ := b7e38567 X0 X1
               grind)
            | exact superpose b7e38567 b7e248
            | (have j0 := b7e248 (k X1 X0) X0
               have j1 := b7e38567 X1 X0
               grind)
            | (have r₁ := b7e248 X1 X1
               have r₂ := b7e38567 X1 X1
               grind)
            | exact resolve b7e248 b7e38567
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e248 b7e38567
          have b7e39384 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (k X1 X0) = (k (k X1 X0) X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e39334 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39334
          have b7e39411 : ∀ X0 X1 : G, (k X1 X0) = (k (k X1 X0) X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e39384 X0 X1
               have j1 := b7e342 X0 X1
               grind)
            | (have r₁ := b7e39384 X0 X1
               have r₂ := b7e342 X0 X1
               grind)
            | exact resolve b7e39384 b7e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e342 b7e39384
          have b7e94205 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e2593 (σ y) x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2593
            | (have r₁ := b7e2593 (σ y) x
               have r₂ := b7e24
               grind)
            | exact resolve b7e2593 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2593
          have b7e94212 : ∀ X0 : G, (σ y) = (k (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e94205 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94205
          have b7e109140 : ∀ X0 : G, (σ y) = (σ (k x (k X0 (τ (σ y))))) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e1140 (σ y) X0 x
               have i₂ := b7e94212 (σ X0)
               grind)
            | exact superpose b7e94212 b7e1140
            | (have j0 := b7e1140 (σ y) X0 x
               have j1 := b7e94212 (σ X0)
               grind)
            | exact resolve b7e1140 b7e94212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1140 b7e94212
          have b7e109215 : ∀ X0 : G, (σ y) = (σ (k x (k X0 (τ (σ y))))) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e109140 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e109140
          have b7e109248 : ∀ X0 : G, (σ y) = (σ (k x (k X0 y))) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e109215 X0
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e109215
            | (have j0 := b7e109215 X0
               grind)
            | exact resolve b7e109215 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e109215
          have b7e201153 : ∀ X0 X1 X2 : G, (k (k X1 X0) X2) = (σ (τ (k (M.op X0 X1) X2))) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e15 (k (k X1 X0) X2)
               have i₂ := b7e8195 X0 X1 X2
               grind)
            | exact superpose b7e8195 b7e15
            | (have j1 := b7e8195 X0 X1 X2
               grind)
            | exact resolve b7e15 b7e8195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8195
          have b7e201168 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = (k (k X1 X0) X2) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e201153 X0 X1 X2
               have i₂ := b7e15 (k (M.op X0 X1) X2)
               grind)
            | exact superpose b7e15 b7e201153
            | (have j0 := b7e201153 X0 X1 X2
               grind)
            | exact resolve b7e201153 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e201153
          have b7e202829 : ∀ X0 X1 : G, (k X1 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e39411 X0 X1
               have i₂ := b7e201168 X0 X1 X0
               grind)
            | exact superpose b7e201168 b7e39411
            | (have j0 := b7e39411 X0 X1
               have j1 := b7e201168 X0 X1 x
               grind)
            | exact resolve b7e39411 b7e201168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39411 b7e201168
          have b7e202900 : ∀ X0 X1 : G, (k X1 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e202829 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e202829
          have b7e204453 : ∀ X0 X1 X2 : G, (k (M.op X2 X1) X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e202900 X2 (M.op x X1)
               have i₂ := b7e33 X1 X2 x
               grind)
            | exact superpose b7e33 b7e202900
            | (have j0 := b7e202900 X0 X1
               grind)
            | exact resolve b7e202900 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e202900
          have b7e212198 : ∀ X0 : G, (k x y) = (k (M.op X0 x) y) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b7e204453 y x x
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e204453
            | exact resolve b7e204453 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93 b7e204453
          have b7e212399 : ∀ X0 : G, (k x y) = (k (M.op X0 x) y) := by
            intro X0
            first
            | (have j0 := b7e212198 X0
               grind)
            | (have r₁ := b7e212198 X0
               have r₂ := b7e122
               grind)
            | exact resolve b7e212198 b7e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e212198
          have b7e212464 : ∀ X0 : G, x = (k (M.op X0 x) y) := by
            intro X0
            first
            | (have i₁ := b7e212399 X0
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e212399
            | exact resolve b7e212399 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58 b7e212399
          have b7e214130 : ∀ X0 : G, (σ y) = (σ (k x x)) ∨ (σ y) = (M.op (σ y) (σ (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b7e109248 (M.op X0 x)
               have i₂ := b7e212464 X0
               grind)
            | exact superpose b7e212464 b7e109248
            | (have j0 := b7e109248 (M.op X0 x)
               grind)
            | exact resolve b7e109248 b7e212464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e109248
          have b7e214174 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b7e214130 X0
               have i₂ := b7e216
               grind)
            | exact superpose b7e216 b7e214130
            | (have j0 := b7e214130 X0
               grind)
            | exact resolve b7e214130 b7e216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216 b7e214130
          have b7e214192 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (M.op X0 x))) := by
            intro X0
            first
            | (have j0 := b7e214174 X0
               grind)
            | (have r₁ := b7e214174 X0
               have r₂ := b7e1336
               grind)
            | exact resolve b7e214174 b7e1336
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1336 b7e214174
          have b7e216553 : ∀ X0 : G, (σ (M.op X0 x)) = (k (σ (M.op X0 x)) (σ y)) ∨ (σ y) = (M.op (σ (M.op X0 x)) (σ (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b7e2192 (σ y) (σ (M.op X0 x))
               have i₂ := b7e214192 X0
               grind)
            | exact superpose b7e214192 b7e2192
            | exact resolve b7e2192 b7e214192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2192 b7e214192
          have b7e216566 : ∀ X0 : G, (σ (M.op X0 x)) = (σ (k (M.op X0 x) y)) ∨ (σ y) = (M.op (σ (M.op X0 x)) (σ (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b7e216553 X0
               have i₂ := b7e19 (M.op X0 x) y
               grind)
            | exact superpose b7e19 b7e216553
            | (have j0 := b7e216553 X0
               grind)
            | exact resolve b7e216553 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216553
          have b7e216575 : ∀ X0 : G, (σ x) = (σ (M.op X0 x)) ∨ (σ y) = (M.op (σ (M.op X0 x)) (σ (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b7e216566 X0
               have i₂ := b7e212464 X0
               grind)
            | exact superpose b7e212464 b7e216566
            | (have j0 := b7e216566 X0
               grind)
            | exact resolve b7e216566 b7e212464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216566
          have b7e216579 : ∀ X0 : G, (σ y) = (σ (M.op X0 x)) ∨ (σ x) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e216575 X0
               have i₂ := b7e1320 X0 x
               grind)
            | exact superpose b7e1320 b7e216575
            | (have j0 := b7e216575 X0
               grind)
            | exact resolve b7e216575 b7e1320
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1320 b7e216575
          have b7e226050 : ∀ X0 : G, (M.op X0 x) = (τ (σ y)) ∨ (σ x) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e14 (M.op X0 x)
               have i₂ := b7e216579 X0
               grind)
            | exact superpose b7e216579 b7e14
            | (have j1 := b7e216579 X0
               grind)
            | exact resolve b7e14 b7e216579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216579
          have b7e226118 : ∀ X0 : G, (σ x) = (σ (M.op X0 x)) ∨ y = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e226050 X0
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e226050
            | (have j0 := b7e226050 X0
               grind)
            | exact resolve b7e226050 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e226050
          have b7e227226 : ∀ X0 : G, (τ (σ x)) = (M.op X0 x) ∨ y = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e14 (M.op X0 x)
               have i₂ := b7e226118 X0
               grind)
            | exact superpose b7e226118 b7e14
            | (have j1 := b7e226118 X0
               grind)
            | exact resolve b7e14 b7e226118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e226118
          have b7e227299 : ∀ X0 : G, y = (M.op X0 x) ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e227226 X0
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e227226
            | (have j0 := b7e227226 X0
               grind)
            | exact resolve b7e227226 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e227226
          have b7e228336 : ∀ X0 : G, x = (k y y) ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e212464 X0
               have i₂ := b7e227299 X0
               grind)
            | exact superpose b7e227299 b7e212464
            | (have j1 := b7e227299 X0
               grind)
            | exact resolve b7e212464 b7e227299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e212464 b7e227299
          have b7e228450 : ∀ X0 : G, x = y ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e228336 X0
               have i₂ := b7e259
               grind)
            | exact superpose b7e259 b7e228336
            | (have j0 := b7e228336 X0
               grind)
            | exact resolve b7e228336 b7e259
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e259 b7e228336
          have b7e228458 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have j0 := b7e228450 X0
               grind)
            | (have r₁ := b7e228450 X0
               have r₂ := b7e122
               grind)
            | exact resolve b7e228450 b7e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e122 b7e228450
          have b7e230073 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X0 x X1
               have i₂ := b7e228458 X0
               grind)
            | exact superpose b7e228458 b7e34
            | exact resolve b7e34 b7e228458
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e228458
          have b7e232253 : (σ y) ≠ (M.op x (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e230073 (σ x) (σ x)
               grind)
            | exact superpose b7e230073 b7e23
            | exact resolve b7e23 b7e230073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e232254 : (σ y) = (M.op x (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e230073 (σ y) (σ x)
               grind)
            | exact superpose b7e230073 b7e24
            | exact resolve b7e24 b7e230073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e230073
          have b7e232554 : False := by grind
          exact b7e232554
        · have b8e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b8e28 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b8e13 (M.op X0 X2) X3 (M.op x X1) X5
               have i₂ := b8e13 X0 X1 X2 x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e29 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 X2 (M.op X3 X1) X4 (M.op X0 x)
               have i₂ := b8e13 X0 X1 x X3
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e30 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b8e31 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e29 x X1 X2 X3 x
               have i₂ := b8e13 X2 X1 x x
               grind)
            | exact superpose b8e13 b8e29
            | exact resolve b8e29 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29
          have b8e32 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e28 X0 x X2 X3 x
               have i₂ := b8e13 X0 X3 x x
               grind)
            | exact superpose b8e13 b8e28
            | exact resolve b8e28 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28
          have b8e54 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (M.op X1 X1) ∨ (k X1 (M.op X0 X2)) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e17 X1 (M.op X0 X2)
               have i₂ := b8e32 X0 X2 X1
               grind)
            | exact superpose b8e32 b8e17
            | (have j0 := b8e17 X1 (M.op X0 X2)
               grind)
            | (have r₁ := b8e17 x (M.op X0 x)
               have r₂ := b8e32 X0 x x
               grind)
            | exact resolve b8e17 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e72 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e73 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X1 X1 X2
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e32 X0 X2 x
               have i₂ := b8e18 X0 (M.op X0 X2)
               grind)
            | exact superpose b8e18 b8e32
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e32 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e81 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b8e105 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e113 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e116 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e105 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e105
            | exact resolve b8e105 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e156 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e72 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e165 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          have b8e179 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e165 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e165
            | exact resolve b8e165 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165
          have b8e183 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e81 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e184 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e183
               have r₂ := b8e24
               grind)
            | exact resolve b8e183 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e183
          have b8e185 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e184
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e184
            | exact resolve b8e184 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184
          have b8e188 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k x y)) X0) := by
            intro X0
            first
            | (have i₁ := b8e32 (σ y) (σ x) X0
               have i₂ := b8e185
               grind)
            | exact superpose b8e185 b8e32
            | exact resolve b8e32 b8e185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e190 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b8e31 (σ x) X0 (σ y)
               have i₂ := b8e185
               grind)
            | exact superpose b8e185 b8e31
            | exact resolve b8e31 b8e185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ (k X0 X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X0) (σ X1)
               have i₂ := b8e71 X0 X1
               grind)
            | exact superpose b8e71 b8e30
            | (have j1 := b8e71 X1 X0
               grind)
            | exact resolve b8e30 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e299 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e71 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e301 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e299 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e299
          have b8e316 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k X0 X1) (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e272 X0 X1
               have i₂ := b8e19 (k X0 X1) (k X0 X1)
               grind)
            | exact superpose b8e19 b8e272
            | (have j0 := b8e272 X0 X1
               grind)
            | exact resolve b8e272 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e272
          have b8e460 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y x)) X0) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e188 X0
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e188
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e188 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e188
          have b8e493 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y x)) X0) ∨ y = (M.op y x) := by
            intro X0
            first
            | (have j0 := b8e460 X0
               grind)
            | (have r₁ := b8e460 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e460 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e460
          have b8e504 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y x)) X0) := by
            intro X0
            first
            | (have j0 := b8e493 X0
               grind)
            | (have r₁ := b8e493 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e493 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e493
          have b8e559 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e190 X0
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e190
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e190 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e190
          have b8e598 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) ∨ y = (M.op y x) := by
            intro X0
            first
            | (have j0 := b8e559 X0
               grind)
            | (have r₁ := b8e559 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e559 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e559
          have b8e613 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) := by
            intro X0
            first
            | (have j0 := b8e598 X0
               grind)
            | (have r₁ := b8e598 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e598 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e598
          have b8e799 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 (M.op X0 X2)) = X1 ∨ (M.op X0 X1) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e156 x (M.op X0 X2)
               have i₂ := b8e32 X0 X2 x
               grind)
            | exact superpose b8e32 b8e156
            | (have j0 := b8e156 X1 X0
               grind)
            | exact resolve b8e156 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32 b8e156
          have b8e882 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e301 (M.op X0 X1)
               have i₂ := b8e30 X0 X1
               grind)
            | exact superpose b8e30 b8e301
            | (have j0 := b8e301 (M.op X0 X1)
               grind)
            | exact resolve b8e301 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e887 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e301 (τ X0)
               have i₂ := b8e27 X0 (τ X0)
               grind)
            | exact superpose b8e27 b8e301
            | (have j0 := b8e301 (τ X0)
               grind)
            | exact resolve b8e301 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27 b8e301
          have b8e890 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b8e882 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e882
          have b8e892 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e887 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e887
            | (have j0 := b8e887 X0
               grind)
            | exact resolve b8e887 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e887
          have b8e896 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e892 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e892
            | (have j0 := b8e892 X0
               grind)
            | exact resolve b8e892 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e892
          have b8e907 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e896 (τ X0)
               have i₂ := b8e116 X0 X0
               grind)
            | exact superpose b8e116 b8e896
            | (have j0 := b8e896 (τ X0)
               grind)
            | exact resolve b8e896 b8e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e896
          have b8e1440 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e73 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e1441 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e1440 X0 X1
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e1440 (k X0 X0) X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e1440 X1 X0
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e1440 (M.op X0 X0) X1
               have r₂ := b8e18 X0 (M.op X1 X1)
               grind)
            | exact resolve b8e1440 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1440
          have b8e1528 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e1441 (σ X0) (σ X1)
               grind)
            | exact superpose b8e1441 b8e19
            | (have j1 := b8e1441 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e1441
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1531 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e113 X1 X0
               have i₂ := b8e1441 X0 (σ X1)
               grind)
            | exact superpose b8e1441 b8e113
            | (have j1 := b8e1441 X0 (σ X1)
               grind)
            | exact resolve b8e113 b8e1441
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1534 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e1441 X0 (τ X1)
               grind)
            | exact superpose b8e1441 b8e26
            | (have j1 := b8e1441 X0 (τ X1)
               grind)
            | exact resolve b8e26 b8e1441
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e1810 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e54 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e2003 : (σ (M.op y x)) = (M.op (σ y) (σ (M.op y x))) := by
            first
            | (have i₁ := b8e504 (σ (M.op y x))
               have i₂ := b8e890 y x
               grind)
            | exact superpose b8e890 b8e504
            | exact resolve b8e504 b8e890
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2027 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e2003
               have i₂ := b8e613 (σ y)
               grind)
            | exact superpose b8e613 b8e2003
            | exact resolve b8e2003 b8e613
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e613 b8e2003
          have b8e2189 : (σ (k x y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e185
               have i₂ := b8e2027
               grind)
            | exact superpose b8e2027 b8e185
            | exact resolve b8e185 b8e2027
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185 b8e2027
          have b8e2283 : (k x y) = (τ (σ (M.op y x))) := by
            first
            | (have i₁ := b8e14 (k x y)
               have i₂ := b8e2189
               grind)
            | exact superpose b8e2189 b8e14
            | exact resolve b8e14 b8e2189
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2189
          have b8e2318 : (M.op y x) = (k x y) := by
            first
            | (have i₁ := b8e2283
               have i₂ := b8e14 (M.op y x)
               grind)
            | exact superpose b8e14 b8e2283
            | exact resolve b8e2283 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2283
          have b8e3356 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e113 X0 (M.op X1 (σ X0))
               have i₂ := b8e1810 X1 (σ X0)
               grind)
            | exact superpose b8e1810 b8e113
            | (have j1 := b8e1810 X1 (σ X0)
               grind)
            | exact resolve b8e113 b8e1810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3365 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e3356 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e3356
            | (have j0 := b8e3356 X0 X1
               grind)
            | exact resolve b8e3356 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3356
          have b8e6269 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e907 (M.op X0 X1)
               have i₂ := b8e30 X0 X1
               grind)
            | exact superpose b8e30 b8e907
            | (have j0 := b8e907 (M.op X0 X1)
               grind)
            | exact resolve b8e907 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e907
          have b8e6282 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b8e6269 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6269
          have b8e6718 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (k (k X0 X1) (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (k X0 X1) (k X0 X1))
               have i₂ := b8e316 X0 X1
               grind)
            | exact superpose b8e316 b8e14
            | (have j1 := b8e316 X0 X1
               grind)
            | exact resolve b8e14 b8e316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e316
          have b8e6789 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X1) (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e6718 X0 X1
               have i₂ := b8e14 (k X0 X1)
               grind)
            | exact superpose b8e14 b8e6718
            | (have j0 := b8e6718 X0 X1
               grind)
            | exact resolve b8e6718 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6718
          have b8e10158 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1534 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e1534
            | exact resolve b8e1534 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1534
          have b8e10285 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e10158 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e10158
            | (have j0 := b8e10158 X0 X1
               grind)
            | exact resolve b8e10158 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10158
          have b8e20642 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1528 x y
               grind)
            | exact superpose b8e1528 b8e20
            | (have j1 := b8e1528 x y
               grind)
            | exact resolve b8e20 b8e1528
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e20695 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e1528 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1528
          have b8e22425 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e20695 (τ X1) (τ X0)
               have i₂ := b8e116 X1 X0
               grind)
            | exact superpose b8e116 b8e20695
            | (have j0 := b8e20695 (τ X1) (τ X0)
               grind)
            | exact resolve b8e20695 b8e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116 b8e20695
          have b8e22490 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e22425 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e22425
            | (have j0 := b8e22425 X0 X1
               grind)
            | exact resolve b8e22425 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22425
          have b8e22502 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e22490 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e22490
            | (have j0 := b8e22490 X0 X1
               grind)
            | exact resolve b8e22490 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22490
          have b8e22510 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e22502 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e22502
            | (have j0 := b8e22502 X0 X1
               grind)
            | exact resolve b8e22502 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22502
          have b8e22514 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e22510 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e22510
            | (have j0 := b8e22510 X0 X1
               grind)
            | exact resolve b8e22510 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22510
          have b8e31978 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20642
               have i₂ := b8e10285 y x
               grind)
            | exact superpose b8e10285 b8e20642
            | (have j1 := b8e10285 (σ y) (σ x)
               grind)
            | (have r₁ := b8e20642
               have r₂ := b8e10285 y x
               grind)
            | exact resolve b8e20642 b8e10285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10285 b8e20642
          have b8e31980 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e31978
          have b8e32534 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e31 (σ y) X0 (σ x)
               have i₂ := b8e31980
               grind)
            | exact superpose b8e31980 b8e31
            | exact resolve b8e31 b8e31980
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32555 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e6282 (σ x) (σ y)
               have i₂ := b8e31980
               grind)
            | exact superpose b8e31980 b8e6282
            | exact resolve b8e6282 b8e31980
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6282
          have b8e32560 : x = (M.op x y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e32555
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e32555
            | exact resolve b8e32555 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32555
          have b8e32742 : x = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e30 x y
               have i₂ := b8e32560
               grind)
            | exact superpose b8e32560 b8e30
            | exact resolve b8e30 b8e32560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e32560
          have b8e32765 : x = (M.op x x) := by
            first
            | (have j1 := b8e22514 x x
               grind)
            | (have r₁ := b8e32742
               have r₂ := b8e22514 x x
               grind)
            | exact resolve b8e32742 b8e22514
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32742
          have b8e32893 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e890 x x
               have i₂ := b8e32765
               grind)
            | exact superpose b8e32765 b8e890
            | exact resolve b8e890 b8e32765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e33528 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e799 (σ x) (σ x) x
               have i₂ := b8e32893
               grind)
            | exact superpose b8e32893 b8e799
            | (have j0 := b8e799 (σ x) (σ x) X0
               grind)
            | (have r₁ := b8e799 (σ x) (σ x) x
               have r₂ := b8e32893
               grind)
            | exact resolve b8e799 b8e32893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e799 b8e32893
          have b8e33533 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e33528 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33528
          have b8e50017 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op (σ x) X0))) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e113 x (M.op (σ x) X0)
               have i₂ := b8e33533 X0
               grind)
            | exact superpose b8e33533 b8e113
            | (have j1 := b8e33533 X0
               grind)
            | exact resolve b8e113 b8e33533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113 b8e33533
          have b8e50082 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e50017 X0
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e50017
            | (have j0 := b8e50017 X0
               grind)
            | exact resolve b8e50017 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50017
          have b8e50397 : ∀ X0 : G, x = (k x (k X0 (τ (σ x)))) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e50082 (σ X0)
               have i₂ := b8e1531 (σ x) X0
               grind)
            | exact superpose b8e1531 b8e50082
            | (have j0 := b8e50082 (σ X0)
               have j1 := b8e1531 (σ x) X0
               grind)
            | exact resolve b8e50082 b8e1531
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1531 b8e50082
          have b8e50455 : ∀ X0 : G, x = (k x (k X0 (τ (σ x)))) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e50397 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50397
          have b8e50467 : ∀ X0 : G, x = (k x (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e50455 X0
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e50455
            | (have j0 := b8e50455 X0
               grind)
            | exact resolve b8e50455 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50455
          have b8e255745 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e3365 y (σ x)
               have i₂ := b8e31980
               grind)
            | exact superpose b8e31980 b8e3365
            | exact resolve b8e3365 b8e31980
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3365 b8e31980
          have b8e255772 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e255745
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e255745
            | exact resolve b8e255745 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e255745
          have b8e260052 : y = (k y (τ (σ x))) ∨ y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e179 y
               have i₂ := b8e255772
               grind)
            | exact superpose b8e255772 b8e179
            | exact resolve b8e179 b8e255772
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e179 b8e255772
          have b8e260118 : y = (k y x) ∨ y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e260052
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e260052
            | exact resolve b8e260052 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e260052
          have b8e260119 : y = (k y x) ∨ x = (M.op x y) := by grind
          clear b8e260118
          have b8e262260 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1441 x y
               have i₂ := b8e260119
               grind)
            | exact superpose b8e260119 b8e1441
            | (have j0 := b8e1441 x y
               grind)
            | exact resolve b8e1441 b8e260119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1441 b8e260119
          have b8e262330 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e262260
          have b8e264502 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e890 x y
               have i₂ := b8e262330
               grind)
            | exact superpose b8e262330 b8e890
            | exact resolve b8e890 b8e262330
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e890 b8e262330
          have b8e284089 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e32534 (σ y)
               have i₂ := b8e264502
               grind)
            | exact superpose b8e264502 b8e32534
            | exact resolve b8e32534 b8e264502
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32534 b8e264502
          have b8e284138 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e284089
          have b8e284148 : x = (M.op x y) := by
            first
            | (have r₁ := b8e284138
               have r₂ := b8e24
               grind)
            | exact resolve b8e284138 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e284138
          have b8e284929 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b8e31 y X0 x
               have i₂ := b8e284148
               grind)
            | exact superpose b8e284148 b8e31
            | exact resolve b8e31 b8e284148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31
          have b8e284954 : y = (k y x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e1810 x y
               have i₂ := b8e284148
               grind)
            | exact superpose b8e284148 b8e1810
            | exact resolve b8e1810 b8e284148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1810 b8e284148
          have b8e285873 : y = (k y (M.op y x)) := by grind
          have b8e287882 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e50467 y
               have i₂ := b8e284954
               grind)
            | exact superpose b8e284954 b8e50467
            | (have j0 := b8e50467 y
               grind)
            | exact resolve b8e50467 b8e284954
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50467 b8e284954
          have b8e287936 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e287882
               have i₂ := b8e2318
               grind)
            | exact superpose b8e2318 b8e287882
            | exact resolve b8e287882 b8e2318
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2318 b8e287882
          have b8e287942 : x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e287936
               have i₂ := b8e284929 y
               grind)
            | exact superpose b8e284929 b8e287936
            | exact resolve b8e287936 b8e284929
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e287936
          have b8e287943 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
          clear b8e287942
          have b8e304804 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e287943
               grind)
            | exact superpose b8e287943 b8e20
            | exact resolve b8e20 b8e287943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e287943
          have b8e304878 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e304804
               have i₂ := b8e284929 x
               grind)
            | exact superpose b8e284929 b8e304804
            | exact resolve b8e304804 b8e284929
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e304804
          have b8e304885 : (σ x) ≠ (σ x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e304878
               have i₂ := b8e32765
               grind)
            | exact superpose b8e32765 b8e304878
            | exact resolve b8e304878 b8e32765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e304878
          have b8e304886 : x = (M.op y x) := by grind
          clear b8e304885
          have b8e307278 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e504 X0
               have i₂ := b8e304886
               grind)
            | exact superpose b8e304886 b8e504
            | exact resolve b8e504 b8e304886
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e504
          have b8e307314 : y = (k y x) := by
            first
            | (have i₁ := b8e285873
               have i₂ := b8e304886
               grind)
            | exact superpose b8e304886 b8e285873
            | exact resolve b8e285873 b8e304886
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e285873 b8e304886
          have b8e309918 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e6789 y x
               have i₂ := b8e307314
               grind)
            | exact superpose b8e307314 b8e6789
            | (have j0 := b8e6789 y x
               grind)
            | exact resolve b8e6789 b8e307314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6789 b8e307314
          have b8e309955 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e309918
               have i₂ := b8e307278 (σ y)
               grind)
            | exact superpose b8e307278 b8e309918
            | exact resolve b8e309918 b8e307278
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e307278 b8e309918
          have b8e309956 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by grind
          clear b8e309955
          have b8e337373 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e309956
               grind)
            | exact superpose b8e309956 b8e20
            | exact resolve b8e20 b8e309956
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309956
          have b8e337447 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k y y) := by
            first
            | (have i₁ := b8e337373
               have i₂ := b8e284929 x
               grind)
            | exact superpose b8e284929 b8e337373
            | exact resolve b8e337373 b8e284929
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e337373
          have b8e337456 : (σ x) ≠ (σ x) ∨ y = (k y y) := by
            first
            | (have i₁ := b8e337447
               have i₂ := b8e32765
               grind)
            | exact superpose b8e32765 b8e337447
            | exact resolve b8e337447 b8e32765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32765 b8e337447
          have b8e337457 : y = (k y y) := by grind
          clear b8e337456
          have b8e339974 : y ≠ y ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e22514 y y
               have i₂ := b8e337457
               grind)
            | exact superpose b8e337457 b8e22514
            | (have j0 := b8e22514 y y
               grind)
            | (have r₁ := b8e22514 y y
               have r₂ := b8e337457
               grind)
            | exact resolve b8e22514 b8e337457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22514 b8e337457
          have b8e339993 : y = (M.op y y) := by grind
          clear b8e339974
          have b8e340048 : y = (M.op y x) := by
            first
            | (have i₁ := b8e339993
               have i₂ := b8e284929 y
               grind)
            | exact superpose b8e284929 b8e339993
            | exact resolve b8e339993 b8e284929
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e284929 b8e339993
          have b8e340092 : False := by grind
          exact b8e340092

/-- `Equation4464`: `x ◇ (y ◇ x) = (z ◇ w) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_x_pxy_Equation4464 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4464 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4464.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X0) := by
        intro X0 X1 X2 X3
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
      have b0e30 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (σ y) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ y) (σ y) X0 X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (σ y) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e34 X0 x
           have i₂ := b0e35 X0 x
           grind)
        | exact superpose b0e35 b0e34
        | exact resolve b0e34 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e40 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e37 (σ y)
           grind)
        | exact superpose b0e37 b0e18
        | exact resolve b0e18 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e44 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
      have b0e46 : (M.op y x) = (k x y) := by grind
      have b0e48 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e44
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e44
        | exact resolve b0e44 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e49 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b0e48
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e48
        | exact resolve b0e48 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e48
      have b0e62 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e35 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e107 : (M.op x (σ y)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e40
           have i₂ := b0e62
           grind)
        | exact superpose b0e62 b0e40
        | exact resolve b0e40 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e62
      have b0e110 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ (M.op y x)) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (σ y) (σ x)
           have i₂ := b0e49
           grind)
        | exact superpose b0e49 b0e11
        | exact resolve b0e11 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e113 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op y x)) X0) := by
        intro X0
        first
        | (have i₁ := b0e110 X0 x
           have i₂ := b0e35 X0 x
           grind)
        | exact superpose b0e35 b0e110
        | exact resolve b0e110 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e110
      have b0e402 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ y)) := by
        first
        | (have i₁ := b0e30 (σ y) (σ x)
           have i₂ := b0e49
           grind)
        | exact superpose b0e49 b0e30
        | exact resolve b0e30 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30 b0e49
      have b0e431 : (M.op x (σ y)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b0e402
           have i₂ := b0e113 (σ y)
           grind)
        | exact superpose b0e113 b0e402
        | exact resolve b0e402 b0e113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113 b0e402
      have b0e438 : False := by grind
      exact b0e438
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X0) := by
          intro X0 X1 X2 X3
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e32 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 y y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 : G, (M.op (σ y) X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e32 X0 x
             have i₂ := b1e33 X0 x
             grind)
          | exact superpose b1e33 b1e32
          | exact resolve b1e32 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e40 : (σ y) = (M.op x (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e35 (σ x)
             grind)
          | exact superpose b1e35 b1e22
          | exact resolve b1e22 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : (M.op y x) = (k x y) := by grind
        have b1e49 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e52 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e49
        have b1e54 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e52
             have r₂ := b1e21
             grind)
          | exact resolve b1e52 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e56 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e54
          | exact resolve b1e54 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e57 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e45
             grind)
          | exact superpose b1e45 b1e56
          | exact resolve b1e56 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45 b1e56
        have b1e60 : (M.op y x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e13
          | exact resolve b1e13 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e61 : x = (M.op y x) := by
          first
          | (have i₁ := b1e60
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e60
          | exact resolve b1e60 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e86 : (M.op (σ x) (σ y)) = (M.op x (σ x)) := by
          first
          | (have i₁ := b1e33 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e33
          | exact resolve b1e33 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e88 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e33 y y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e33
          | exact resolve b1e33 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e96 : x = (M.op x y) := by
          first
          | (have i₁ := b1e88
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e88
          | exact resolve b1e88 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61 b1e88
        have b1e97 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e86
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e86
          | exact resolve b1e86 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e86
        have b1e110 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k (τ X0) X1)
             have i₂ := b1e24 X0 X1
             grind)
          | exact superpose b1e24 b1e13
          | exact resolve b1e13 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e113 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        clear b1e25
        have b1e121 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op x (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e113 X0
             have i₂ := b1e33 (τ X0) (τ X0)
             grind)
          | exact superpose b1e33 b1e113
          | exact resolve b1e113 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e113
        have b1e213 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e97
             grind)
          | exact superpose b1e97 b1e19
          | exact resolve b1e19 b1e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e97
        have b1e225 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e213
             have i₂ := b1e96
             grind)
          | exact superpose b1e96 b1e213
          | exact resolve b1e213 b1e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e96 b1e213
        have b1e1647 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e68 y y
             grind)
          | exact superpose b1e68 b1e21
          | (have j1 := b1e68 y y
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e68 x y
             grind)
          | exact resolve b1e21 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e1733 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e1647
        have b1e1784 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op x (σ y)) := by
          first
          | (have i₁ := b1e1733
             have i₂ := b1e35 (σ y)
             grind)
          | exact superpose b1e35 b1e1733
          | exact resolve b1e1733 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1733
        have b1e2687 : ∀ X0 : G, (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) = (τ (σ (M.op x (τ (σ X0))))) := by
          intro X0
          first
          | (have i₁ := b1e110 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
             have i₂ := b1e121 (σ X0)
             grind)
          | exact superpose b1e121 b1e110
          | exact resolve b1e110 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e110 b1e121
        have b1e2688 : ∀ X0 : G, (M.op x (τ (σ X0))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
          intro X0
          first
          | (have i₁ := b1e2687 X0
             have i₂ := b1e13 (M.op x (τ (σ X0)))
             grind)
          | exact superpose b1e13 b1e2687
          | exact resolve b1e2687 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2687
        have b1e2699 : ∀ X0 : G, (M.op x (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b1e2688 X0
             have i₂ := b1e13 (M.op (τ (σ X0)) (τ (σ X0)))
             grind)
          | exact superpose b1e13 b1e2688
          | exact resolve b1e2688 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2688
        have b1e2706 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e2699 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e2699
          | exact resolve b1e2699 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2699
        have b1e2716 : (M.op x (σ y)) = (k (M.op x (σ y)) (σ y)) := by
          first
          | (have i₁ := b1e2706 (σ y)
             have i₂ := b1e35 (σ y)
             grind)
          | exact superpose b1e35 b1e2706
          | exact resolve b1e2706 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e2706
        have b1e2825 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e1784
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e1784
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e1784 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1784
        have b1e2829 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by grind
        clear b1e2825
        have b1e2836 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e2829
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e2829
          | exact resolve b1e2829 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2829
        have b1e2837 : (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by grind
        clear b1e2836
        have b1e2841 : (σ y) = (M.op x (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e2837
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e2837
          | exact resolve b1e2837 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2837
        have b1e2843 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e2716
             have i₂ := b1e2841
             grind)
          | exact superpose b1e2841 b1e2716
          | exact resolve b1e2716 b1e2841
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2716 b1e2841
        have b1e2886 : (σ y) = (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b1e2843
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e2843
          | exact resolve b1e2843 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2843
        have b1e3367 : (σ y) = (σ (M.op y y)) ∨ x = y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e2886
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e2886
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e2886 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2886
        have b1e3382 : (σ y) = (σ (M.op y y)) ∨ x = y ∨ y = (M.op y y) := by grind
        clear b1e3367
        have b1e3396 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e3382
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e3382
          | exact resolve b1e3382 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3382
        have b1e3403 : x = y ∨ y = (M.op y y) := by
          first
          | (have r₁ := b1e3396
             have r₂ := b1e225
             grind)
          | exact resolve b1e3396 b1e225
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3396
        have b1e3410 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e3403
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e3403
          | exact resolve b1e3403 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3403
        have b1e3411 : x = y := by grind
        clear b1e3410
        have b1e3515 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e225
             have i₂ := b1e3411
             grind)
          | exact superpose b1e3411 b1e225
          | exact resolve b1e225 b1e3411
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e225 b1e3411
        have b1e3522 : False := by grind
        exact b1e3522
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X0) := by
          intro X0 X1 X2 X3
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e29 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 y y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b2e29 y y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e46 : (M.op y x) = (k x y) := by grind
        have b2e67 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1077 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e67 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e1078 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1077
             have r₂ := b2e22
             grind)
          | exact resolve b2e1077 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1077
        have b2e1079 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1078
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1078
          | exact resolve b2e1078 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1078
        have b2e1080 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b2e1079
             have i₂ := b2e46
             grind)
          | exact superpose b2e46 b2e1079
          | exact resolve b2e1079 b2e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46 b2e1079
        have b2e1082 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e1080
             grind)
          | exact superpose b2e1080 b2e19
          | exact resolve b2e19 b2e1080
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1080
        have b2e1110 : (σ (M.op y x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b2e1082
             have i₂ := b2e34
             grind)
          | exact superpose b2e34 b2e1082
          | exact resolve b2e1082 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e1082
        have b2e1111 : False := by grind
        exact b2e1111
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X0) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e32 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 (σ y) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e32 X0 x
             have i₂ := b3e33 X0 x
             grind)
          | exact superpose b3e33 b3e32
          | exact resolve b3e32 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e38 : (σ (M.op x y)) ≠ (M.op y (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e35 (σ y)
             grind)
          | exact superpose b3e35 b3e19
          | exact resolve b3e19 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e42 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b3e45 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e42
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e42
          | exact resolve b3e42 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e49 : (M.op (σ y) (σ x)) = (M.op y (σ y)) := by
          first
          | (have i₁ := b3e33 (σ y) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e33
          | exact resolve b3e33 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : y = (M.op x y) := by
          first
          | (have i₁ := b3e33 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e33
          | exact resolve b3e33 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e67 : y ≠ y ∨ x = (M.op y y) ∨ x = (k x y) := by
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
        have b3e68 : x = (M.op y y) ∨ x = (k x y) := by grind
        clear b3e67
        have b3e69 : x = (k x y) := by
          first
          | (have r₁ := b3e68
             have r₂ := b3e20
             grind)
          | exact resolve b3e68 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e99 : (σ y) ≠ (M.op y (σ y)) := by
          first
          | (have i₁ := b3e38
             have i₂ := b3e51
             grind)
          | exact superpose b3e51 b3e38
          | exact resolve b3e38 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e51
        have b3e245 : (M.op y (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e45
             have i₂ := b3e49
             grind)
          | exact superpose b3e49 b3e45
          | exact resolve b3e45 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e49
        have b3e255 : (σ x) = (M.op y (σ y)) := by
          first
          | (have i₁ := b3e245
             have i₂ := b3e69
             grind)
          | exact superpose b3e69 b3e245
          | exact resolve b3e245 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e69 b3e245
        have b3e408 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e99
             have i₂ := b3e255
             grind)
          | exact superpose b3e255 b3e99
          | exact resolve b3e99 b3e255
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e99 b3e255
        have b3e1133 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e79 y y
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e79
          | exact resolve b3e79 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e1216 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by grind
        clear b3e1133
        have b3e1265 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b3e1216
             have r₂ := b3e408
             grind)
          | exact resolve b3e1216 b3e408
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e408 b3e1216
        have b3e1311 : (k y y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e1265
             grind)
          | exact superpose b3e1265 b3e13
          | exact resolve b3e13 b3e1265
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1265
        have b3e1331 : x = (k y y) := by
          first
          | (have i₁ := b3e1311
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1311
          | exact resolve b3e1311 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1311
        have b3e1379 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e1331
             grind)
          | exact superpose b3e1331 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e1331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1380 : x = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b3e1379
        have b3e1384 : y = (M.op y y) := by
          first
          | (have r₁ := b3e1380
             have r₂ := b3e20
             grind)
          | exact resolve b3e1380 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1380
        have b3e1525 : (M.op y y) = (k y y) := by grind
        clear b3e1384
        have b3e1536 : x = (M.op y y) := by
          first
          | (have i₁ := b3e1525
             have i₂ := b3e1331
             grind)
          | exact superpose b3e1331 b3e1525
          | exact resolve b3e1525 b3e1331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1331 b3e1525
        have b3e1537 : False := by grind
        exact b3e1537
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e38 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e38 X0 x
               have i₂ := b4e39 X0 x
               grind)
            | exact superpose b4e39 b4e38
            | exact resolve b4e38 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e46 : (σ y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e41 (σ x)
               grind)
            | exact superpose b4e41 b4e24
            | exact resolve b4e24 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e91 : y = (M.op x y) := by
            first
            | (have i₁ := b4e39 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e39
            | exact resolve b4e39 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e92 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e39 (σ x) y
               have i₂ := b4e46
               grind)
            | exact superpose b4e46 b4e39
            | exact resolve b4e39 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e46
          have b4e118 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e92
               grind)
            | exact superpose b4e92 b4e20
            | exact resolve b4e20 b4e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92
          have b4e126 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e118
               have i₂ := b4e91
               grind)
            | exact superpose b4e91 b4e118
            | exact resolve b4e118 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91 b4e118
          have b4e127 : False := by grind
          exact b4e127
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b5e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e14
            | exact resolve b5e14 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op (M.op X3 X2) (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e13 (M.op X3 X2) X2 X4 X5
               have i₂ := b5e13 X2 X3 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : y = (M.op x y) := by
            first
            | (have i₁ := b5e35 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e35
            | exact resolve b5e35 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 (M.op X1 X0) X0
               have i₂ := b5e35 X0 X1
               grind)
            | exact superpose b5e35 b5e35
            | exact resolve b5e35 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e45 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X0) = (M.op y X0) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e13 X0 x X2 X3
               have i₂ := b5e35 X0 x
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op y (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e41 X0 X1
               have i₂ := b5e45 (M.op y X0) X1 X0
               grind)
            | exact superpose b5e45 b5e41
            | exact resolve b5e41 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e57 : y ≠ y ∨ x = (M.op y y) ∨ x = (k x y) := by
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
          have b5e58 : x = (M.op y y) ∨ x = (k x y) := by grind
          clear b5e57
          have b5e59 : x = (k x y) := by
            first
            | (have r₁ := b5e58
               have r₂ := b5e21
               grind)
            | exact resolve b5e58 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e67 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op X1 (τ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e26 X0 X1
               have i₂ := b5e18 (τ X0) X1
               grind)
            | exact superpose b5e18 b5e26
            | (have j1 := b5e18 (τ X0) X1
               grind)
            | exact resolve b5e26 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e71 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X0 X3) = (M.op X0 X3) ∨ (M.op X3 X0) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X3 X3
               have i₂ := b5e18 X0 X3
               grind)
            | (have i₁ := b5e13 X0 X1 X2 X3
               have i₂ := b5e18 (M.op X2 X3) X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X3
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e74 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e76 : ∀ X0 X1 X3 : G, (k X0 X3) = (M.op X0 X3) ∨ (M.op X0 X1) = (M.op y X1) ∨ (M.op X3 X0) = X3 := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e71 X0 X1 x X3
               have i₂ := b5e35 X1 x
               grind)
            | exact superpose b5e35 b5e71
            | (have j0 := b5e71 X0 X1 x X3
               grind)
            | exact resolve b5e71 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e91 : ∀ X0 X1 X2 : G, (M.op y (M.op X1 X2)) = (M.op y (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35 (M.op X1 X2) X0
               have i₂ := b5e45 (M.op X0 (M.op X1 X2)) X1 X2
               grind)
            | exact superpose b5e45 b5e35
            | exact resolve b5e35 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e103 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          have b5e108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e111 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op y (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e103 X0
               have i₂ := b5e35 (τ X0) (τ X0)
               grind)
            | exact superpose b5e35 b5e103
            | exact resolve b5e103 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103
          have b5e430 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1))) = (k (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            by_contra hcon
            push Not at hcon
            have f430_15 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op (M.op X3 X2) (M.op (M.op X0 X1) X2)) := by
              intro X0 X1 X2 X3 X4 X5
              grind
            have f430_16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have f430_19 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have f430_25 : y = (M.op y x) := by grind
            have f430_28 : (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1))) ≠ (k (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) (M.op X0 X1)) := by grind
            have f430_39 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
              intro X0 X1
              first
              | (have i₁ := f430_16 X0 X1 y x
                 have i₂ := f430_25
                 grind)
              | exact superpose f430_25 f430_16
              | exact resolve f430_16 f430_25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f430_49 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X0) = (M.op y X0) := by
              intro X0 X2 X3
              first
              | (have i₁ := f430_16 X0 x X2 X3
                 have i₂ := f430_39 X0 x
                 grind)
              | exact superpose f430_39 f430_16
              | exact resolve f430_16 f430_39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f430_231 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y (M.op X0 X1))) = (k (M.op y (M.op X0 X1)) (M.op X0 X1)) := by
              intro X0 X1
              grind
            have f430_232 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (k (M.op y (M.op X0 X1)) (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := f430_231 X0 X1
                 have i₂ := f430_39 (M.op X0 X1) y
                 grind)
              | exact superpose f430_39 f430_231
              | exact resolve f430_231 f430_39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f430_312 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) ≠ (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := f430_28
                 have i₂ := f430_15 X0 X1 X1 (M.op X2 X3) X0 X1
                 grind)
              | (have i₁ := f430_28
                 have i₂ := f430_15 X2 X3 X1 X0 x x
                 grind)
              | exact superpose f430_15 f430_28
              | exact resolve f430_28 f430_15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f430_316 : (M.op (M.op X0 X1) (M.op y (M.op X0 X1))) ≠ (k (M.op y (M.op X0 X1)) (M.op X0 X1)) := by
              first
              | (have i₁ := f430_312 x x
                 have i₂ := f430_49 (M.op X0 X1) x x
                 grind)
              | exact superpose f430_49 f430_312
              | exact resolve f430_312 f430_49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f430_320 : (M.op y (M.op X0 X1)) ≠ (M.op (M.op X0 X1) (M.op y (M.op X0 X1))) := by
              first
              | (have i₁ := f430_316
                 have i₂ := f430_232 X0 X1
                 grind)
              | exact superpose f430_232 f430_316
              | exact resolve f430_316 f430_232
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f430_324 : False := by
              first
              | (have r₁ := f430_320
                 have r₂ := f430_39 (M.op X0 X1) y
                 grind)
              | exact resolve f430_320 f430_39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            exact f430_324
          clear b5e32
          have b5e457 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op y (M.op (M.op X2 X3) X1))) = (k (M.op y (M.op (M.op X2 X3) X1)) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e430 X2 X3 X2 X3
               have i₂ := b5e45 (M.op (M.op X2 X3) X3) X2 X3
               grind)
            | exact superpose b5e45 b5e430
            | exact resolve b5e430 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e430
          have b5e507 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y (M.op y X1))) = (k (M.op y (M.op y X1)) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e457 X0 X0 x x
               have i₂ := b5e50 X0 (M.op x x)
               grind)
            | exact superpose b5e50 b5e457
            | exact resolve b5e457 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e457
          have b5e553 : ∀ X0 X1 : G, (k (M.op y (M.op y X1)) (M.op X0 X1)) = (M.op y (M.op y (M.op y X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e507 X0 X1
               have i₂ := b5e45 (M.op y (M.op y X1)) X0 X1
               grind)
            | exact superpose b5e45 b5e507
            | exact resolve b5e507 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e507
          have b5e587 : ∀ X0 X1 : G, (M.op y (M.op y X1)) = (k (M.op y (M.op y X1)) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e553 X0 X1
               have i₂ := b5e91 y y X1
               grind)
            | exact superpose b5e91 b5e553
            | exact resolve b5e553 b5e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91 b5e553
          have b5e748 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e73 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e849 : ∀ X0 : G, (σ x) ≠ (M.op y (σ y)) ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e76 (σ y) (σ y) X0
               grind)
            | exact superpose b5e76 b5e23
            | (have j1 := b5e76 (σ y) x X0
               grind)
            | exact resolve b5e23 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1059 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e74 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74
          have b5e1060 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1059
               have r₂ := b5e24
               grind)
            | exact resolve b5e1059 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1059
          have b5e1061 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1060
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1060
            | exact resolve b5e1060 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1060
          have b5e1062 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1061
               have i₂ := b5e59
               grind)
            | exact superpose b5e59 b5e1061
            | exact resolve b5e1061 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e1061
          have b5e1064 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e1062
               grind)
            | exact superpose b5e1062 b5e20
            | exact resolve b5e20 b5e1062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1076 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e45 X0 (σ x) (σ y)
               have i₂ := b5e1062
               grind)
            | exact superpose b5e1062 b5e45
            | exact resolve b5e45 b5e1062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1092 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e1064
               have i₂ := b5e40
               grind)
            | exact superpose b5e40 b5e1064
            | exact resolve b5e1064 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e1064
          have b5e1172 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e66 y y
               grind)
            | exact superpose b5e66 b5e23
            | (have j1 := b5e66 y y
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e66 x y
               grind)
            | exact resolve b5e23 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1213 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op y (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 (σ X1) (σ X1)
               have i₂ := b5e66 X0 X1
               grind)
            | exact superpose b5e66 b5e35
            | (have j1 := b5e66 X0 X1
               grind)
            | exact resolve b5e35 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1240 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e66 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e1241 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e1240 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1240
          have b5e1247 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e1172
          have b5e1341 : (σ x) = (M.op y (σ y)) := by
            first
            | (have i₁ := b5e1062
               have i₂ := b5e1076 (σ y)
               grind)
            | exact superpose b5e1076 b5e1062
            | exact resolve b5e1062 b5e1076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1062 b5e1076
          have b5e1616 : ∀ X0 : G, (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) = (τ (σ (M.op y (τ (σ X0))))) := by
            intro X0
            first
            | (have i₁ := b5e31 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
               have i₂ := b5e111 (σ X0)
               grind)
            | exact superpose b5e111 b5e31
            | exact resolve b5e31 b5e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e1617 : ∀ X0 : G, (M.op y (τ (σ X0))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
            intro X0
            first
            | (have i₁ := b5e1616 X0
               have i₂ := b5e14 (M.op y (τ (σ X0)))
               grind)
            | exact superpose b5e14 b5e1616
            | exact resolve b5e1616 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1616
          have b5e1625 : ∀ X0 : G, (M.op y (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b5e1617 X0
               have i₂ := b5e14 (M.op (τ (σ X0)) (τ (σ X0)))
               grind)
            | exact superpose b5e14 b5e1617
            | exact resolve b5e1617 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1617
          have b5e1632 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e1625 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1625
            | exact resolve b5e1625 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1625
          have b5e2626 : ∀ X0 : G, (M.op y y) = (k (M.op y y) (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e587 X0 y
               have i₂ := b5e35 y y
               grind)
            | exact superpose b5e35 b5e587
            | exact resolve b5e587 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e587
          have b5e2751 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e1241 (M.op y y)
               have i₂ := b5e2626 y
               grind)
            | exact superpose b5e2626 b5e1241
            | (have j0 := b5e1241 (M.op y y)
               grind)
            | exact resolve b5e1241 b5e2626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1241
          have b5e2757 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
          clear b5e2751
          have b5e2781 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e1247
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e1247
            | (have j1 := b5e18 (σ y) (σ y)
               grind)
            | exact resolve b5e1247 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1247
          have b5e2782 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e2781
          have b5e4164 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e111 X0
               have i₂ := b5e67 X0 (τ X0)
               grind)
            | exact superpose b5e67 b5e111
            | (have j1 := b5e67 X0 (τ X0)
               grind)
            | exact resolve b5e111 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e111
          have b5e4253 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have j0 := b5e4164 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4164
          have b5e4292 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e4253 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e4253
            | (have j0 := b5e4253 X0
               grind)
            | exact resolve b5e4253 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4253
          have b5e4422 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e849 X0
               have i₂ := b5e1341
               grind)
            | exact superpose b5e1341 b5e849
            | (have j0 := b5e849 X0
               grind)
            | (have r₁ := b5e849 X0
               have r₂ := b5e1341
               grind)
            | exact resolve b5e849 b5e1341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e849
          have b5e4424 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b5e4422 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4422
          have b5e4488 : (M.op y (σ (M.op y y))) = (k (σ (M.op y y)) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e1632 (σ (M.op y y))
               have i₂ := b5e2757
               grind)
            | exact superpose b5e2757 b5e1632
            | exact resolve b5e1632 b5e2757
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1632 b5e2757
          have b5e4525 : (σ (k (M.op y y) (M.op y y))) = (M.op y (σ (M.op y y))) := by
            first
            | (have i₁ := b5e4488
               have i₂ := b5e19 (M.op y y) (M.op y y)
               grind)
            | exact superpose b5e19 b5e4488
            | exact resolve b5e4488 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4488
          have b5e4538 : (σ (M.op y y)) = (M.op y (σ (M.op y y))) := by
            first
            | (have i₁ := b5e4525
               have i₂ := b5e2626 y
               grind)
            | exact superpose b5e2626 b5e4525
            | exact resolve b5e4525 b5e2626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2626 b5e4525
          have b5e9168 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e108 y X0
               have i₂ := b5e4424 X0
               grind)
            | exact superpose b5e4424 b5e108
            | (have j1 := b5e4424 X0
               grind)
            | exact resolve b5e108 b5e4424
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108
          have b5e10968 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op y (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op y (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e748 (σ X0) (σ X1)
               have i₂ := b5e1213 X0 X1
               grind)
            | exact superpose b5e1213 b5e748
            | (have j0 := b5e748 (σ X1) (σ X0)
               have j1 := b5e1213 X1 X0
               grind)
            | exact resolve b5e748 b5e1213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e748
          have b5e10982 : ∀ X0 X1 : G, (σ X0) ≠ (M.op y (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e1213 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1213
          have b5e10992 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op y (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e10968 X0 X1
               have j1 := b5e76 (σ X1) X1 (σ X0)
               grind)
            | (have r₁ := b5e10968 X0 X1
               have r₂ := b5e76 (σ X1) (σ X0) x
               grind)
            | exact resolve b5e10968 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76 b5e10968
          have b5e11053 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e10992 X0 X1
               have j1 := b5e10982 X0 X1
               grind)
            | (have r₁ := b5e10992 X0 X1
               have r₂ := b5e10982 X0 X1
               grind)
            | exact resolve b5e10992 b5e10982
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10982 b5e10992
          have b5e11072 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e11053 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e11053
            | (have j0 := b5e11053 X0 X1
               grind)
            | exact resolve b5e11053 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11053
          have b5e11073 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e11072 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11072
          have b5e11955 : ∀ X0 : G, (τ (M.op y (σ y))) = (k y (τ (M.op X0 (σ y)))) ∨ (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e9168 (M.op X0 (σ y))
               have i₂ := b5e35 (σ y) X0
               grind)
            | exact superpose b5e35 b5e9168
            | (have j0 := b5e9168 (M.op X0 (σ y))
               grind)
            | exact resolve b5e9168 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9168
          have b5e11994 : ∀ X0 : G, (τ (σ x)) = (k y (τ (M.op X0 (σ y)))) ∨ (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e11955 X0
               have i₂ := b5e1341
               grind)
            | exact superpose b5e1341 b5e11955
            | (have j0 := b5e11955 X0
               grind)
            | exact resolve b5e11955 b5e1341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11955
          have b5e12012 : ∀ X0 : G, x = (k y (τ (M.op X0 (σ y)))) ∨ (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e11994 X0
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e11994
            | (have j0 := b5e11994 X0
               grind)
            | exact resolve b5e11994 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11994
          have b5e12023 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y (σ y)) ∨ x = (k y (τ (M.op X0 (σ y)))) := by
            intro X0
            first
            | (have i₁ := b5e12012 X0
               have i₂ := b5e45 (σ y) X0 (σ y)
               grind)
            | exact superpose b5e45 b5e12012
            | (have j0 := b5e12012 X0
               grind)
            | exact resolve b5e12012 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45 b5e12012
          have b5e12028 : ∀ X0 : G, x = (k y (τ (M.op X0 (σ y)))) ∨ (σ x) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e12023 X0
               have i₂ := b5e1341
               grind)
            | exact superpose b5e1341 b5e12023
            | (have j0 := b5e12023 X0
               grind)
            | exact resolve b5e12023 b5e1341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12023
          have b5e42979 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e11073 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e11073
            | exact resolve b5e11073 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11073
          have b5e43401 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e42979 X0 X1
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e42979
            | (have j0 := b5e42979 X0 X1
               grind)
            | exact resolve b5e42979 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e42979
          have b5e43473 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e43401 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e43401
            | exact resolve b5e43401 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43401
          have b5e45158 : (k (M.op (σ y) (σ y)) (σ y)) = (σ (M.op y (τ (σ y)))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e4292 (σ y)
               have i₂ := b5e4424 (σ y)
               grind)
            | exact superpose b5e4424 b5e4292
            | (have j0 := b5e4292 (σ y)
               have j1 := b5e4424 (σ y)
               grind)
            | exact resolve b5e4292 b5e4424
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4292 b5e4424
          have b5e45279 : (σ (M.op y y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e45158
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e45158
            | exact resolve b5e45158 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45158
          have b5e45320 : (σ (M.op y y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e45279
          have b5e45356 : (M.op y (σ y)) = (σ (M.op y y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e45320
               have i₂ := b5e35 (σ y) (σ y)
               grind)
            | exact superpose b5e35 b5e45320
            | exact resolve b5e45320 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e45320
          have b5e45376 : (σ x) = (σ (M.op y y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e45356
               have i₂ := b5e1341
               grind)
            | exact superpose b5e1341 b5e45356
            | exact resolve b5e45356 b5e1341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45356
          have b5e45384 : y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e45376
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e45376
            | exact resolve b5e45376 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45376
          have b5e45390 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b5e45384
               have r₂ := b5e2782
               grind)
            | exact resolve b5e45384 b5e2782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2782 b5e45384
          have b5e45439 : x = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e12028 (σ y)
               have i₂ := b5e45390
               grind)
            | exact superpose b5e45390 b5e12028
            | exact resolve b5e12028 b5e45390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12028 b5e45390
          have b5e45537 : x = (k y (τ (σ y))) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b5e45439
               have r₂ := b5e1092
               grind)
            | exact resolve b5e45439 b5e1092
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45439
          have b5e45553 : x = (k y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e45537
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e45537
            | exact resolve b5e45537 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45537
          have b5e46307 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e43473 y y
               have i₂ := b5e45553
               grind)
            | exact superpose b5e45553 b5e43473
            | (have j0 := b5e43473 y y
               grind)
            | exact resolve b5e43473 b5e45553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43473 b5e45553
          have b5e46310 : x = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b5e46307
          have b5e46339 : y = (M.op y y) := by
            first
            | (have r₁ := b5e46310
               have r₂ := b5e21
               grind)
            | exact resolve b5e46310 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46310
          have b5e46815 : (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b5e4538
               have i₂ := b5e46339
               grind)
            | exact superpose b5e46339 b5e4538
            | exact resolve b5e4538 b5e46339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4538 b5e46339
          have b5e48970 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1341
               have i₂ := b5e46815
               grind)
            | exact superpose b5e46815 b5e1341
            | exact resolve b5e1341 b5e46815
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1341 b5e46815
          have b5e49101 : False := by grind
          exact b5e49101
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X0) := by
          intro X0 X1 X2 X3
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e30 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (σ y) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b6e40 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e39
          | exact resolve b6e39 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e55 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e30 (σ y) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e30
          | exact resolve b6e30 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e67 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e55
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e55
          | exact resolve b6e55 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e55
        have b6e696 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e67
             grind)
          | exact superpose b6e67 b6e19
          | exact resolve b6e19 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e751 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e696
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e696
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e696 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e696
        have b6e752 : x = (M.op y y) ∨ y = (M.op y x) := by grind
        clear b6e751
        have b6e754 : y = (M.op y x) := by
          first
          | (have r₁ := b6e752
             have r₂ := b6e20
             grind)
          | exact resolve b6e752 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e752
        have b6e756 : False := by grind
        exact b6e756
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b7e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e26 X0 X1
               grind)
            | exact superpose b7e26 b7e14
            | exact resolve b7e14 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e32 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X1) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ x) (σ y) X0 X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b7e13 X2 x X4 X5
               have i₂ := b7e13 X2 x X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b7e49 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          have b7e50 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (σ y) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e49 X0
               have i₂ := b7e36 (τ X0) (τ X0)
               grind)
            | exact superpose b7e36 b7e49
            | exact resolve b7e49 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e51 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e36 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e36
            | exact resolve b7e36 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e63 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e67 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e63
          have b7e70 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e23
               grind)
            | exact resolve b7e67 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e72 : (σ x) = (σ (k x y)) := by
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
          have b7e75 : (k x y) = (τ (σ x)) := by
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
          have b7e76 : x = (k x y) := by
            first
            | (have i₁ := b7e75
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e75
            | exact resolve b7e75 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e86 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e36 X1 X1
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e36 X0 X1
               have i₂ := b7e18 (M.op X1 X0) X1
               grind)
            | exact superpose b7e18 b7e36
            | (have j1 := b7e18 X0 X1
               grind)
            | exact resolve b7e36 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e87 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X0 X3) = (M.op X0 X3) ∨ (M.op X3 X0) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X2 X3 X3
               have i₂ := b7e18 X0 X3
               grind)
            | (have i₁ := b7e13 X0 X1 X2 X3
               have i₂ := b7e18 (M.op X2 X3) X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X0 X3
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e92 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (σ y) X1) ∨ (k X0 X3) = (M.op X0 X3) ∨ (M.op X3 X0) = X3 := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e87 X0 X1 x X3
               have i₂ := b7e36 X1 x
               grind)
            | exact superpose b7e36 b7e87
            | (have j0 := b7e87 X0 X1 x X3
               grind)
            | exact resolve b7e87 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e96 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e76
               grind)
            | exact superpose b7e76 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e97 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e96
               have r₂ := b7e21
               grind)
            | exact resolve b7e96 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e99 : x = (M.op x y) := by
            first
            | (have r₁ := b7e97
               have r₂ := b7e22
               grind)
            | exact resolve b7e97 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97
          have b7e176 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op x X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e35 x y X0 X1 X2
               have i₂ := b7e99
               grind)
            | exact superpose b7e99 b7e35
            | exact resolve b7e35 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e178 : (M.op y x) = (M.op (σ y) y) := by
            first
            | (have i₁ := b7e36 y x
               have i₂ := b7e99
               grind)
            | exact superpose b7e99 b7e36
            | exact resolve b7e36 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e309 : (M.op (σ x) (σ y)) = (M.op x (σ x)) := by
            first
            | (have i₁ := b7e32 x y
               have i₂ := b7e99
               grind)
            | exact superpose b7e99 b7e32
            | exact resolve b7e32 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e331 : (σ y) = (M.op x (σ x)) := by
            first
            | (have i₁ := b7e309
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e309
            | exact resolve b7e309 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51 b7e309
          have b7e670 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e89 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e813 : ∀ X0 : G, (M.op (σ y) X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e176 X0 x (σ x)
               have i₂ := b7e331
               grind)
            | exact superpose b7e331 b7e176
            | exact resolve b7e176 b7e331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e176 b7e331
          have b7e944 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b7e178
               have i₂ := b7e813 y
               grind)
            | exact superpose b7e813 b7e178
            | exact resolve b7e178 b7e813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e975 : x = (M.op y x) := by
            first
            | (have i₁ := b7e944
               have i₂ := b7e99
               grind)
            | exact superpose b7e99 b7e944
            | exact resolve b7e944 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e944
          have b7e1110 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e82 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e1111 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e1110 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1110
          have b7e1277 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e975
               grind)
            | exact superpose b7e975 b7e22
            | exact resolve b7e22 b7e975
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3553 : ∀ X0 : G, (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) = (τ (σ (M.op (σ y) (τ (σ X0))))) := by
            intro X0
            first
            | (have i₁ := b7e31 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
               have i₂ := b7e50 (σ X0)
               grind)
            | exact superpose b7e50 b7e31
            | exact resolve b7e31 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e3556 : ∀ X0 : G, (M.op (σ y) (τ (σ X0))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
            intro X0
            first
            | (have i₁ := b7e3553 X0
               have i₂ := b7e14 (M.op (σ y) (τ (σ X0)))
               grind)
            | exact superpose b7e14 b7e3553
            | exact resolve b7e3553 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3553
          have b7e3585 : ∀ X0 : G, (M.op (σ y) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b7e3556 X0
               have i₂ := b7e14 (M.op (τ (σ X0)) (τ (σ X0)))
               grind)
            | exact superpose b7e14 b7e3556
            | exact resolve b7e3556 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3556
          have b7e3605 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e3585 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e3585
            | exact resolve b7e3585 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3585
          have b7e3615 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e3605 X0
               have i₂ := b7e813 X0
               grind)
            | exact superpose b7e813 b7e3605
            | exact resolve b7e3605 b7e813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3605
          have b7e3637 : (M.op x (σ y)) = (k (M.op x (σ y)) (σ y)) := by
            first
            | (have i₁ := b7e3615 (σ y)
               have i₂ := b7e813 (σ y)
               grind)
            | exact superpose b7e813 b7e3615
            | exact resolve b7e3615 b7e813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3856 : (τ (M.op x (σ y))) = (k (τ (M.op x (σ y))) y) := by
            first
            | (have i₁ := b7e31 (M.op x (σ y)) y
               have i₂ := b7e3637
               grind)
            | exact superpose b7e3637 b7e31
            | exact resolve b7e31 b7e3637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e3637
          have b7e3872 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e1111 (τ X0)
               have i₂ := b7e27 X0 (τ X0)
               grind)
            | exact superpose b7e27 b7e1111
            | (have j0 := b7e1111 (τ X0)
               grind)
            | exact resolve b7e1111 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27 b7e1111
          have b7e3875 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e3872 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e3872
            | (have j0 := b7e3872 X0
               grind)
            | exact resolve b7e3872 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3872
          have b7e3878 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e3875 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e3875
            | (have j0 := b7e3875 X0
               grind)
            | exact resolve b7e3875 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3875
          have b7e6434 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (σ y) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op (σ y) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e670 X0 X1
               have i₂ := b7e86 X0 X1
               grind)
            | (have i₁ := b7e670 X1 (σ y)
               have i₂ := b7e86 X0 X1
               grind)
            | exact superpose b7e86 b7e670
            | (have j0 := b7e670 X1 X0
               have j1 := b7e86 X1 X0
               grind)
            | (have r₁ := b7e670 (σ y) X1
               have r₂ := b7e86 (σ y) X1
               grind)
            | (have r₁ := b7e670 X1 (σ y)
               have r₂ := b7e86 (σ y) X1
               grind)
            | exact resolve b7e670 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e670
          have b7e6563 : ∀ X0 X1 : G, (M.op (σ y) X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e86 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e6566 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (σ y) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op (σ y) X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e6434 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6434
          have b7e6569 : ∀ X0 X1 : G, (M.op x X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e6563 X0 X1
               have i₂ := b7e813 X0
               grind)
            | exact superpose b7e813 b7e6563
            | (have j0 := b7e6563 X0 X1
               grind)
            | exact resolve b7e6563 b7e813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6563
          have b7e6654 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op (σ y) X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e6566 X0 X1
               have j1 := b7e92 X1 X1 X0
               grind)
            | (have r₁ := b7e6566 X1 X0
               have r₂ := b7e92 X0 X1 x
               grind)
            | (have r₁ := b7e6566 X1 (σ y)
               have r₂ := b7e92 (σ y) X1 x
               grind)
            | (have r₁ := b7e6566 X0 (M.op (σ y) X0)
               have r₂ := b7e92 X0 X1 (M.op (σ y) X0)
               grind)
            | exact resolve b7e6566 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92 b7e6566
          have b7e6765 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e6654 X0 X1
               have i₂ := b7e813 X0
               grind)
            | exact superpose b7e813 b7e6654
            | (have j0 := b7e6654 X0 X1
               grind)
            | exact resolve b7e6654 b7e813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6654
          have b7e6841 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e6765 X0 X1
               have j1 := b7e6569 X0 X1
               grind)
            | (have r₁ := b7e6765 X0 X1
               have r₂ := b7e6569 X0 X1
               grind)
            | (have r₁ := b7e6765 x x
               have r₂ := b7e6569 x X1
               grind)
            | exact resolve b7e6765 b7e6569
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6569 b7e6765
          have b7e7955 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e46 X0 X1
               have i₂ := b7e6841 X1 (σ X0)
               grind)
            | exact superpose b7e6841 b7e46
            | (have j1 := b7e6841 X1 (σ X0)
               grind)
            | exact resolve b7e46 b7e6841
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e23506 : ∀ X0 : G, (τ (M.op x X0)) = (k y (τ X0)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e7955 y X0
               have i₂ := b7e813 X0
               grind)
            | exact superpose b7e813 b7e7955
            | (have j0 := b7e7955 y X0
               grind)
            | exact resolve b7e7955 b7e813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7955
          have b7e27056 : (k y (τ (σ y))) = (k (k y (τ (σ y))) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e3856
               have i₂ := b7e23506 (σ y)
               grind)
            | exact superpose b7e23506 b7e3856
            | (have j1 := b7e23506 (σ y)
               grind)
            | exact resolve b7e3856 b7e23506
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e23506
          have b7e27086 : (k y y) = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e27056
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e27056
            | exact resolve b7e27056 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27056
          have b7e27109 : (k y y) = (k (k y y) y) ∨ (σ y) = (M.op x (σ y)) := by
            first
            | (have i₁ := b7e27086
               have i₂ := b7e813 (σ y)
               grind)
            | exact superpose b7e813 b7e27086
            | exact resolve b7e27086 b7e813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e813 b7e27086
          have b7e35213 : (M.op y y) = (k (M.op y y) y) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e27109
               have i₂ := b7e6841 y y
               grind)
            | exact superpose b7e6841 b7e27109
            | (have j1 := b7e6841 y y
               grind)
            | exact resolve b7e27109 b7e6841
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6841 b7e27109
          have b7e35247 : (M.op y y) = (M.op y (M.op y y)) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by grind
          clear b7e35213
          have b7e35253 : (M.op y y) = (M.op (σ y) y) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e35247
               have i₂ := b7e36 y y
               grind)
            | exact superpose b7e36 b7e35247
            | exact resolve b7e35247 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e35247
          have b7e35256 : (M.op y y) = (M.op y x) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e35253
               have i₂ := b7e178
               grind)
            | exact superpose b7e178 b7e35253
            | exact resolve b7e35253 b7e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e178 b7e35253
          have b7e35259 : x = (M.op y y) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e35256
               have i₂ := b7e975
               grind)
            | exact superpose b7e975 b7e35256
            | exact resolve b7e35256 b7e975
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e975 b7e35256
          have b7e35262 : (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b7e35259
               have r₂ := b7e21
               grind)
            | exact resolve b7e35259 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35259
          have b7e35768 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e3856
               have i₂ := b7e35262
               grind)
            | exact superpose b7e35262 b7e3856
            | exact resolve b7e3856 b7e35262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3856 b7e35262
          have b7e35851 : y = (k y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e35768
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e35768
            | exact resolve b7e35768 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35768
          have b7e35858 : y = (M.op y y) := by
            first
            | (have j1 := b7e3878 y
               grind)
            | (have r₁ := b7e35851
               have r₂ := b7e3878 y
               grind)
            | exact resolve b7e35851 b7e3878
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3878 b7e35851
          have b7e36340 : (M.op x y) = (k y y) := by
            first
            | (have i₁ := b7e3615 y
               have i₂ := b7e35858
               grind)
            | exact superpose b7e35858 b7e3615
            | exact resolve b7e3615 b7e35858
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3615
          have b7e36341 : (M.op y y) = (k y y) := by grind
          have b7e36411 : y = (k y y) := by
            first
            | (have i₁ := b7e36341
               have i₂ := b7e35858
               grind)
            | exact superpose b7e35858 b7e36341
            | exact resolve b7e36341 b7e35858
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35858 b7e36341
          have b7e36412 : x = (k y y) := by
            first
            | (have i₁ := b7e36340
               have i₂ := b7e99
               grind)
            | exact superpose b7e99 b7e36340
            | exact resolve b7e36340 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99 b7e36340
          have b7e36438 : x = y := by
            first
            | (have i₁ := b7e36412
               have i₂ := b7e36411
               grind)
            | exact superpose b7e36411 b7e36412
            | exact resolve b7e36412 b7e36411
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36411 b7e36412
          have b7e36460 : False := by grind
          exact b7e36460
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e81 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e452 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e81 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e453 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e452
               have r₂ := b8e24
               grind)
            | exact resolve b8e452 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e452
          have b8e454 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e453
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e453
            | exact resolve b8e453 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e453
          have b8e455 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e454
               grind)
            | exact superpose b8e454 b8e20
            | exact resolve b8e20 b8e454
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e454
          have b8e572 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e455
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e455
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e455 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e455
          have b8e573 : x = (M.op y y) ∨ y = (M.op y x) := by grind
          clear b8e572
          have b8e575 : y = (M.op y x) := by
            first
            | (have r₁ := b8e573
               have r₂ := b8e21
               grind)
            | exact resolve b8e573 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e573
          have b8e577 : False := by grind
          exact b8e577

/-- `Equation4514`: `x ◇ (y ◇ z) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_x_pyx_Equation4514 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4514 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4514.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e34 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e11 y X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e34 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e34
        | exact resolve b0e34 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e44 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e45 : (M.op x y) = (k x y) := by grind
      have b0e46 : (M.op y x) = (k x y) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e45
        | exact resolve b0e45 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e47 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e44
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e44
        | exact resolve b0e44 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e48 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e47
        | exact resolve b0e47 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e47
      have b0e82 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e18
        | exact resolve b0e18 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e87 : (σ (M.op y x)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e82
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e82
        | exact resolve b0e82 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e82
      have b0e88 : False := by grind
      exact b0e88
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
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
        have b1e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e29 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e12 y X0 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X0 X1 X2
             have i₂ := b1e12 X0 X3 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e33 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e33
          | exact resolve b1e33 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e43 : (M.op x y) = (k x y) := by grind
        have b1e44 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b1e43
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e43
          | exact resolve b1e43 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e47 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e50 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e47
        have b1e52 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e50
             have r₂ := b1e21
             grind)
          | exact resolve b1e50 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e53 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e52
          | exact resolve b1e52 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e54 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e44
             grind)
          | exact superpose b1e44 b1e53
          | exact resolve b1e53 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e53
        have b1e57 : (M.op y x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e13
          | exact resolve b1e13 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e58 : x = (M.op y x) := by
          first
          | (have i₁ := b1e57
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e57
          | exact resolve b1e57 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b1e70 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e12 y X0 x
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e12
          | exact resolve b1e12 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e72 : ∀ X0 : G, (M.op y x) = (M.op y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e70 X0
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e70
          | exact resolve b1e70 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e73 : ∀ X0 : G, x = (M.op y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e72 X0
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e72
          | exact resolve b1e72 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58 b1e72
        have b1e78 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k (τ X0) X1)
             have i₂ := b1e25 X0 X1
             grind)
          | exact superpose b1e25 b1e13
          | exact resolve b1e13 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e79 : (σ y) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e24
          | exact resolve b1e24 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e36
        have b1e85 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e79
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e79
          | exact resolve b1e79 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e79
        have b1e101 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 (σ y)
             have i₂ := b1e29 X0
             grind)
          | exact superpose b1e29 b1e12
          | exact resolve b1e12 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e104 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 (M.op X0 (σ y)) X0
             have i₂ := b1e29 X0
             grind)
          | exact superpose b1e29 b1e12
          | exact resolve b1e12 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e141 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e34 X1 X2 X0 (M.op X0 (σ y))
             have i₂ := b1e29 X0
             grind)
          | exact superpose b1e29 b1e34
          | exact resolve b1e34 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e177 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e141 X0 X1 X2
             have i₂ := b1e101 X1 X0
             grind)
          | exact superpose b1e101 b1e141
          | exact resolve b1e141 b1e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101 b1e141
        have b1e197 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op X0 (M.op X2 (M.op X1 x))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e34 X0 y (M.op X1 x) X2
             have i₂ := b1e73 X1
             grind)
          | exact superpose b1e73 b1e34
          | exact resolve b1e34 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e73
        have b1e202 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e197 X0 x x
             have i₂ := b1e177 (M.op x x) X0 x
             grind)
          | exact superpose b1e177 b1e197
          | exact resolve b1e197 b1e177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e197
        have b1e4147 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
          intro X0
          grind
        clear b1e78
        have b1e4153 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ y)))) := by
          intro X0
          first
          | (have i₁ := b1e4147 X0
             have i₂ := b1e104 (σ X0) (σ X0)
             grind)
          | exact superpose b1e104 b1e4147
          | exact resolve b1e4147 b1e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104 b1e4147
        have b1e4157 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e4153 X0
             have i₂ := b1e177 (σ y) (σ X0) (σ X0)
             grind)
          | exact superpose b1e177 b1e4153
          | exact resolve b1e4153 b1e177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e177 b1e4153
        have b1e4159 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) x)) := by
          intro X0
          first
          | (have i₁ := b1e4157 X0
             have i₂ := b1e202 (σ X0)
             grind)
          | exact superpose b1e202 b1e4157
          | exact resolve b1e4157 b1e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4157
        have b1e4205 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e63 y y
             grind)
          | exact superpose b1e63 b1e21
          | (have j1 := b1e63 y y
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e63 y x
             grind)
          | exact resolve b1e21 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e4301 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e4205
        have b1e4370 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) x) := by
          first
          | (have i₁ := b1e4301
             have i₂ := b1e202 (σ y)
             grind)
          | exact superpose b1e202 b1e4301
          | exact resolve b1e4301 b1e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4301
        have b1e8413 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e4370
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e4370
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e4370 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4370
        have b1e8416 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) x) ∨ y = (M.op y y) := by grind
        clear b1e8413
        have b1e8421 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e8416
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e8416
          | exact resolve b1e8416 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8416
        have b1e8422 : (σ y) = (M.op (σ y) x) ∨ y = (M.op y y) := by grind
        clear b1e8421
        have b1e8425 : (σ y) = (M.op (σ y) x) ∨ x = y := by
          first
          | (have i₁ := b1e8422
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e8422
          | exact resolve b1e8422 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8422
        have b1e9184 : ∀ X0 : G, (k (σ (τ (M.op (σ (τ X0)) (σ (τ X0))))) X0) = (σ (τ (M.op (σ (τ X0)) x))) := by
          intro X0
          first
          | (have i₁ := b1e26 X0 (τ (M.op (σ (τ X0)) (σ (τ X0))))
             have i₂ := b1e4159 (τ X0)
             grind)
          | exact superpose b1e4159 b1e26
          | exact resolve b1e26 b1e4159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e4159
        have b1e9186 : ∀ X0 : G, (M.op (σ (τ X0)) x) = (k (σ (τ (M.op (σ (τ X0)) (σ (τ X0))))) X0) := by
          intro X0
          first
          | (have i₁ := b1e9184 X0
             have i₂ := b1e14 (M.op (σ (τ X0)) x)
             grind)
          | exact superpose b1e14 b1e9184
          | exact resolve b1e9184 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9184
        have b1e9202 : ∀ X0 : G, (M.op (σ (τ X0)) x) = (k (M.op (σ (τ X0)) (σ (τ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b1e9186 X0
             have i₂ := b1e14 (M.op (σ (τ X0)) (σ (τ X0)))
             grind)
          | exact superpose b1e14 b1e9186
          | exact resolve b1e9186 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9186
        have b1e9211 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e9202 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e9202
          | exact resolve b1e9202 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9202
        have b1e10299 : (M.op (σ y) x) = (k (M.op (σ y) x) (σ y)) := by
          first
          | (have i₁ := b1e9211 (σ y)
             have i₂ := b1e202 (σ y)
             grind)
          | exact superpose b1e202 b1e9211
          | exact resolve b1e9211 b1e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e202 b1e9211
        have b1e11473 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e10299
             have i₂ := b1e8425
             grind)
          | exact superpose b1e8425 b1e10299
          | exact resolve b1e10299 b1e8425
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8425 b1e10299
        have b1e11492 : (σ y) = (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b1e11473
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e11473
          | exact resolve b1e11473 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11473
        have b1e12635 : (σ y) = (σ (M.op y y)) ∨ x = y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e11492
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e11492
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e11492 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11492
        have b1e12658 : (σ y) = (σ (M.op y y)) ∨ x = y ∨ y = (M.op y y) := by grind
        clear b1e12635
        have b1e12680 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e12658
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12658
          | exact resolve b1e12658 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12658
        have b1e12686 : x = y ∨ y = (M.op y y) := by
          first
          | (have r₁ := b1e12680
             have r₂ := b1e85
             grind)
          | exact resolve b1e12680 b1e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12680
        have b1e12691 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e12686
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12686
          | exact resolve b1e12686 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12686
        have b1e12692 : x = y := by grind
        clear b1e12691
        have b1e12724 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e85
             have i₂ := b1e12692
             grind)
          | exact superpose b1e12692 b1e85
          | exact resolve b1e85 b1e12692
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e85 b1e12692
        have b1e12741 : False := by grind
        exact b1e12741
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 X0 (M.op X3 X1)
             have i₂ := b2e12 X0 X3 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 (M.op X0 X2) X0
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e12 y X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e12 X0 X3 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b2e28 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e28
          | exact resolve b2e28 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : (M.op x y) = (k x y) := by grind
        have b2e41 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b2e40
             have i₂ := b2e32
             grind)
          | exact superpose b2e32 b2e40
          | exact resolve b2e40 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e40
        have b2e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b2e53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e57 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e24 X0 X1
             grind)
          | exact superpose b2e24 b2e13
          | exact resolve b2e13 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
        have b2e84 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X2 (M.op X1 y))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e31 X0 y (M.op X1 y) X2
             have i₂ := b2e28 X1
             grind)
          | exact superpose b2e28 b2e31
          | exact resolve b2e31 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e99 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b2e31 X0 X1 y y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e31
          | exact resolve b2e31 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e129 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X2 x)) := by
          intro X0 X2
          first
          | (have i₁ := b2e84 X0 x X2
             have i₂ := b2e99 X2 x
             grind)
          | exact superpose b2e99 b2e84
          | exact resolve b2e84 b2e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e132 : ∀ X0 X2 : G, (M.op X0 x) = (M.op X0 (M.op X2 x)) := by
          intro X0 X2
          first
          | (have i₁ := b2e129 X0 X2
             have i₂ := b2e99 X0 x
             grind)
          | exact superpose b2e99 b2e129
          | exact resolve b2e129 b2e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e129
        have b2e190 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op (M.op X1 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e27 X0 x y X1
             have i₂ := b2e99 X0 x
             grind)
          | exact superpose b2e99 b2e27
          | exact resolve b2e27 b2e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e99
        have b2e218 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X1 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e190 X0 X1
             have i₂ := b2e132 X1 X0
             grind)
          | exact superpose b2e132 b2e190
          | exact resolve b2e190 b2e132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e132 b2e190
        have b2e327 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op X0 (M.op X4 X3)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e31 X0 (M.op X3 X2) X3 X4
             have i₂ := b2e26 X3 X2 X0 X1
             grind)
          | exact superpose b2e26 b2e31
          | exact resolve b2e31 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e31
        have b2e343 : ∀ X0 X3 X4 : G, (M.op X0 x) = (M.op X0 (M.op X4 X3)) := by
          intro X0 X3 X4
          first
          | (have i₁ := b2e327 X0 x x X3 X4
             have i₂ := b2e218 (M.op x x) X0
             grind)
          | exact superpose b2e218 b2e327
          | exact resolve b2e327 b2e218
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e327
        have b2e1580 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e57 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e1581 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e1580
             have r₂ := b2e22
             grind)
          | exact resolve b2e1580 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1580
        have b2e1582 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1581
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1581
          | exact resolve b2e1581 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1581
        have b2e1583 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b2e1582
             have i₂ := b2e41
             grind)
          | exact superpose b2e41 b2e1582
          | exact resolve b2e1582 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41 b2e1582
        have b2e2305 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
          intro X0
          grind
        clear b2e66
        have b2e2311 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) x)) := by
          intro X0
          first
          | (have i₁ := b2e2305 X0
             have i₂ := b2e218 (σ X0) (σ X0)
             grind)
          | exact superpose b2e218 b2e2305
          | exact resolve b2e2305 b2e218
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e218 b2e2305
        have b2e2817 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e52 y y
             grind)
          | exact superpose b2e52 b2e21
          | (have j1 := b2e52 y y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e52 y x
             grind)
          | exact resolve b2e21 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e2908 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e2817
        have b2e11602 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e2908
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e2908
          | (have j1 := b2e17 (σ y) (σ y)
             grind)
          | exact resolve b2e2908 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2908
        have b2e11605 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e11602
        have b2e11610 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e11605
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e11605
          | exact resolve b2e11605 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11605
        have b2e11611 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e11610
        have b2e11614 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e11611
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e11611
          | exact resolve b2e11611 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11611
        have b2e13105 : (τ (M.op (σ y) x)) = (k (τ (σ y)) y) ∨ x = y := by
          first
          | (have i₁ := b2e2311 y
             have i₂ := b2e11614
             grind)
          | exact superpose b2e11614 b2e2311
          | exact resolve b2e2311 b2e11614
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2311
        have b2e13143 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e343 X0 (σ y) (σ y)
             have i₂ := b2e11614
             grind)
          | exact superpose b2e11614 b2e343
          | exact resolve b2e343 b2e11614
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e343
        have b2e13178 : (k y y) = (τ (M.op (σ y) x)) ∨ x = y := by
          first
          | (have i₁ := b2e13105
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e13105
          | exact resolve b2e13105 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13105
        have b2e15729 : (σ y) = (M.op (σ y) x) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b2e11614
             have i₂ := b2e13143 (σ y)
             grind)
          | exact superpose b2e13143 b2e11614
          | exact resolve b2e11614 b2e13143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11614 b2e13143
        have b2e15740 : (σ y) = (M.op (σ y) x) ∨ x = y := by grind
        clear b2e15729
        have b2e18840 : (k y y) = (τ (σ y)) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b2e13178
             have i₂ := b2e15740
             grind)
          | exact superpose b2e15740 b2e13178
          | exact resolve b2e13178 b2e15740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13178 b2e15740
        have b2e18848 : (k y y) = (τ (σ y)) ∨ x = y := by grind
        clear b2e18840
        have b2e18850 : y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e18848
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e18848
          | exact resolve b2e18848 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18848
        have b2e20524 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e53 y y
             have i₂ := b2e18850
             grind)
          | exact superpose b2e18850 b2e53
          | (have j0 := b2e53 y y
             grind)
          | exact resolve b2e53 b2e18850
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e18850
        have b2e20525 : y = (M.op y y) ∨ x = y := by grind
        clear b2e20524
        have b2e20535 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e20525
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e20525
          | exact resolve b2e20525 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20525
        have b2e20536 : x = y := by grind
        clear b2e20535
        have b2e22621 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1583
             have i₂ := b2e20536
             grind)
          | exact superpose b2e20536 b2e1583
          | exact resolve b2e1583 b2e20536
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1583 b2e20536
        have b2e22636 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e22621
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e22621
          | exact resolve b2e22621 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22621
        have b2e22650 : False := by grind
        exact b2e22650
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e47 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e46
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e46
          | exact resolve b3e46 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e52 : y ≠ y ∨ x = (M.op y y) ∨ x = (k x y) := by
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
        have b3e55 : x = (M.op y y) ∨ x = (k x y) := by grind
        clear b3e52
        have b3e57 : x = (k x y) := by
          first
          | (have r₁ := b3e55
             have r₂ := b3e20
             grind)
          | exact resolve b3e55 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b3e64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e105 : (σ y) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e47
             grind)
          | exact superpose b3e47 b3e24
          | exact resolve b3e24 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e47
        have b3e111 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e105
             have i₂ := b3e57
             grind)
          | exact superpose b3e57 b3e105
          | exact resolve b3e105 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57 b3e105
        have b3e4663 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e62 y y
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e62
          | exact resolve b3e62 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62
        have b3e4779 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by grind
        clear b3e4663
        have b3e4855 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b3e4779
             have r₂ := b3e111
             grind)
          | exact resolve b3e4779 b3e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111 b3e4779
        have b3e4960 : (k y y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e4855
             grind)
          | exact superpose b3e4855 b3e13
          | exact resolve b3e13 b3e4855
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4855
        have b3e4980 : x = (k y y) := by
          first
          | (have i₁ := b3e4960
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e4960
          | exact resolve b3e4960 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4960
        have b3e5024 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e64 y y
             have i₂ := b3e4980
             grind)
          | exact superpose b3e4980 b3e64
          | (have j0 := b3e64 y y
             grind)
          | exact resolve b3e64 b3e4980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64
        have b3e5025 : x = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b3e5024
        have b3e5029 : y = (M.op y y) := by
          first
          | (have r₁ := b3e5025
             have r₂ := b3e20
             grind)
          | exact resolve b3e5025 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5025
        have b3e5215 : (M.op y y) = (k y y) := by grind
        clear b3e5029
        have b3e5237 : x = (M.op y y) := by
          first
          | (have i₁ := b3e5215
             have i₂ := b3e4980
             grind)
          | exact superpose b3e4980 b3e5215
          | exact resolve b3e5215 b3e4980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4980 b3e5215
        have b3e5242 : False := by grind
        exact b3e5242
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b5e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X0 (M.op X3 X1)
               have i₂ := b5e13 X0 X3 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op X0 X2) X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op y x) := by
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
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 (M.op X3 X1))) = (M.op (M.op (M.op X0 X1) X0) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X2 (M.op X3 X1)
               have i₂ := b5e13 X0 X3 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e13 X0 X3 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b5e31 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e31
            | exact resolve b5e31 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e42 : y = (M.op y x) := by
            first
            | (have i₁ := b5e35
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e35
            | exact resolve b5e35 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e45 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 x
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e13
            | exact resolve b5e13 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e48 : y ≠ y ∨ x = (M.op y y) ∨ x = (k x y) := by
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
          have b5e51 : x = (M.op y y) ∨ x = (k x y) := by grind
          clear b5e48
          have b5e53 : x = (k x y) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e21
               grind)
            | exact resolve b5e51 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b5e59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e61 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 (M.op X0 X2) X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X1
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e64 : ∀ X0 X1 : G, (M.op y y) = (M.op y (M.op x (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e45 (M.op x X1)
               have i₂ := b5e13 x X0 X1
               grind)
            | exact superpose b5e13 b5e45
            | exact resolve b5e45 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e68 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X1 x))) = (M.op (M.op y y) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 y X0 (M.op X1 x)
               have i₂ := b5e45 X1
               grind)
            | exact superpose b5e45 b5e13
            | exact resolve b5e13 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e69 : ∀ X0 : G, (M.op (M.op y y) y) = (M.op (M.op y X0) y) := by
            intro X0
            first
            | (have i₁ := b5e68 X0 x
               have i₂ := b5e30 X0 x x y
               grind)
            | exact superpose b5e30 b5e68
            | exact resolve b5e68 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68
          have b5e70 : (M.op y y) = (M.op (M.op y x) y) := by
            first
            | (have i₁ := b5e64 x x
               have i₂ := b5e30 x x x y
               grind)
            | exact superpose b5e30 b5e64
            | exact resolve b5e64 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e71 : (M.op y y) = (M.op (M.op y y) y) := by
            first
            | (have i₁ := b5e70
               have i₂ := b5e69 x
               grind)
            | exact superpose b5e69 b5e70
            | exact resolve b5e70 b5e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69 b5e70
          have b5e76 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b5e89 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e122 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (M.op X2 X3)) ∨ (M.op X3 X0) = (k X0 X3) ∨ (M.op X0 X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e34 X1 X2 X3 X3
               have i₂ := b5e18 X0 X3
               grind)
            | (have i₁ := b5e34 X0 X1 X2 X3
               have i₂ := b5e18 (M.op X3 X2) X1
               grind)
            | exact superpose b5e18 b5e34
            | (have j1 := b5e18 X0 X3
               grind)
            | exact resolve b5e34 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e125 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e34 X0 X1 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e34
            | exact resolve b5e34 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e172 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) X0) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e125 X0 x
               grind)
            | exact superpose b5e125 b5e13
            | exact resolve b5e13 b5e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e223 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op X1 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 X0 x y X1
               have i₂ := b5e125 X0 x
               grind)
            | exact superpose b5e125 b5e30
            | exact resolve b5e30 b5e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e251 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X1 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e223 X0 X1
               have i₂ := b5e125 X1 X0
               grind)
            | exact superpose b5e125 b5e223
            | exact resolve b5e223 b5e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e125 b5e223
          have b5e310 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X3) (M.op (M.op X4 X1) X4)) = (M.op (M.op (M.op X0 X1) (M.op X2 X3)) (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e29 X4 X1 (M.op (M.op X0 X1) X3) X0
               have i₂ := b5e13 (M.op X0 X1) X2 X3
               grind)
            | exact superpose b5e13 b5e29
            | exact resolve b5e29 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e357 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X3) X2)) = (M.op (M.op (M.op X0 X1) (M.op X4 X3)) (M.op X5 X1)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e34 (M.op (M.op X0 X1) (M.op X4 X3)) X0 X1 X5
               have i₂ := b5e29 X2 X3 (M.op X0 X1) X4
               grind)
            | exact superpose b5e29 b5e34
            | exact resolve b5e34 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e367 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op X0 (M.op X4 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 X0 (M.op X3 X2) X3 X4
               have i₂ := b5e29 X3 X2 X0 X1
               grind)
            | exact superpose b5e29 b5e34
            | exact resolve b5e34 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29 b5e34
          have b5e383 : ∀ X0 X3 X4 : G, (M.op X0 y) = (M.op X0 (M.op X4 X3)) := by
            intro X0 X3 X4
            first
            | (have i₁ := b5e367 X0 x x X3 X4
               have i₂ := b5e251 (M.op x x) X0
               grind)
            | exact superpose b5e251 b5e367
            | exact resolve b5e367 b5e251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e367
          have b5e388 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X4 X3)) (M.op X5 X1)) = (M.op (M.op X0 X1) (M.op X2 y)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e357 X0 X1 X2 X3 X4 X5
               have i₂ := b5e251 X3 X2
               grind)
            | exact superpose b5e251 b5e357
            | exact resolve b5e357 b5e251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e357
          have b5e416 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X3)) (M.op (M.op X0 X1) X3)) = (M.op (M.op (M.op X0 X1) X3) (M.op X4 y)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e310 X0 X1 X2 X3 X4
               have i₂ := b5e251 X1 X4
               grind)
            | exact superpose b5e251 b5e310
            | exact resolve b5e310 b5e251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e310
          have b5e446 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X4 X3)) (M.op X5 X1)) = (M.op (M.op X0 X1) y) := by
            intro X0 X1 X3 X4 X5
            first
            | (have i₁ := b5e388 X0 X1 x X3 X4 X5
               have i₂ := b5e383 (M.op X0 X1) y x
               grind)
            | exact superpose b5e383 b5e388
            | exact resolve b5e388 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e388
          have b5e462 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X3)) (M.op (M.op X0 X1) X3)) = (M.op (M.op (M.op X0 X1) X3) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e416 X0 X1 X2 X3 x
               have i₂ := b5e383 (M.op (M.op X0 X1) X3) y x
               grind)
            | exact superpose b5e383 b5e416
            | exact resolve b5e416 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e416
          have b5e478 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) y) = (M.op (M.op (M.op X0 X1) (M.op X4 X3)) y) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b5e446 X0 X1 X3 X4 x
               have i₂ := b5e383 (M.op (M.op X0 X1) (M.op X4 X3)) X1 x
               grind)
            | exact superpose b5e383 b5e446
            | exact resolve b5e446 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e446
          have b5e486 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X3) y) = (M.op (M.op (M.op X0 X1) (M.op X2 X3)) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e462 X0 X1 X2 X3
               have i₂ := b5e383 (M.op (M.op X0 X1) (M.op X2 X3)) X3 (M.op X0 X1)
               grind)
            | exact superpose b5e383 b5e462
            | exact resolve b5e462 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e462
          have b5e493 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op (M.op X0 X1) y) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e478 X0 X1 x x
               have i₂ := b5e383 (M.op X0 X1) x x
               grind)
            | exact superpose b5e383 b5e478
            | exact resolve b5e478 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e478
          have b5e501 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X3) y) = (M.op (M.op (M.op X0 X1) y) y) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e486 X0 X1 x X3
               have i₂ := b5e383 (M.op X0 X1) X3 x
               grind)
            | exact superpose b5e383 b5e486
            | exact resolve b5e486 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e486
          have b5e506 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) y) = (M.op (M.op (M.op X0 X1) X3) y) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e501 X0 X1 X3
               have i₂ := b5e493 X0 X1
               grind)
            | exact superpose b5e493 b5e501
            | exact resolve b5e501 b5e493
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e501
          have b5e548 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) y) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) y) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b5e564 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) y) = (k (M.op (M.op X0 X1) y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e548 X0 X1
               have i₂ := b5e383 (M.op (M.op X0 X1) y) X1 X0
               grind)
            | exact superpose b5e383 b5e548
            | exact resolve b5e548 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e548
          have b5e578 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (k (M.op (M.op X0 X1) y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e564 X0 X1
               have i₂ := b5e493 X0 X1
               grind)
            | exact superpose b5e493 b5e564
            | exact resolve b5e564 b5e493
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e564
          have b5e681 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) (M.op (M.op X0 X3) X0)) = (M.op (M.op (M.op X0 X3) X0) (M.op X0 (M.op X4 X5))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e30 X0 X4 X5 (M.op (M.op X0 X3) X0)
               have i₂ := b5e32 X0 X3 X1 X2
               grind)
            | exact superpose b5e32 b5e30
            | exact resolve b5e30 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e32
          have b5e704 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) (M.op (M.op X0 X3) X0)) = (M.op (M.op (M.op X0 X3) X0) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e681 X0 X1 X2 X3 x x
               have i₂ := b5e383 (M.op (M.op X0 X3) X0) (M.op x x) X0
               grind)
            | exact superpose b5e383 b5e681
            | exact resolve b5e681 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e681
          have b5e785 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) (M.op (M.op X0 X3) X0)) = (M.op (M.op X0 X3) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e704 X0 X1 X2 X3
               have i₂ := b5e506 X0 X3 X0
               grind)
            | exact superpose b5e506 b5e704
            | exact resolve b5e704 b5e506
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e704
          have b5e831 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) y) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e785 X0 X1 X2 X3
               have i₂ := b5e383 (M.op X0 (M.op X1 (M.op X2 X3))) X0 (M.op X0 X3)
               grind)
            | exact superpose b5e383 b5e785
            | exact resolve b5e785 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e785
          have b5e856 : ∀ X0 X3 : G, (M.op (M.op X0 y) y) = (M.op (M.op X0 X3) y) := by
            intro X0 X3
            first
            | (have i₁ := b5e831 X0 x x X3
               have i₂ := b5e383 X0 (M.op x X3) x
               grind)
            | exact superpose b5e383 b5e831
            | exact resolve b5e831 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e831
          have b5e1558 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1559 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e1563 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e76 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e76
            | exact resolve b5e76 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e1576 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e63 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e1577 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e1576
               have r₂ := b5e24
               grind)
            | exact resolve b5e1576 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1576
          have b5e1578 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1577
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1577
            | exact resolve b5e1577 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1577
          have b5e1579 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e1578
               have i₂ := b5e53
               grind)
            | exact superpose b5e53 b5e1578
            | exact resolve b5e1578 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e1578
          have b5e1593 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e383 X0 (σ x) (σ y)
               have i₂ := b5e1579
               grind)
            | exact superpose b5e1579 b5e383
            | exact resolve b5e383 b5e1579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1750 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e61 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1753 : ∀ X0 X1 : G, (M.op X1 y) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e1750 X0 X1 x
               have i₂ := b5e383 X1 X1 x
               grind)
            | exact superpose b5e383 b5e1750
            | (have j0 := b5e1750 X0 X1 x
               grind)
            | exact resolve b5e1750 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1750
          have b5e1935 : (σ x) = (M.op (σ y) y) := by
            first
            | (have i₁ := b5e1579
               have i₂ := b5e1593 (σ y)
               grind)
            | exact superpose b5e1593 b5e1579
            | exact resolve b5e1579 b5e1593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1579 b5e1593
          have b5e2341 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e251 y (σ y)
               have i₂ := b5e1935
               grind)
            | exact superpose b5e1935 b5e251
            | exact resolve b5e251 b5e1935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2492 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e2341
               grind)
            | exact superpose b5e2341 b5e24
            | exact resolve b5e24 b5e2341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2341
          have b5e2951 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e57 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e2952 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e2951 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2951
          have b5e3381 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 y) y) y) = (M.op (M.op (M.op X0 X1) X2) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e856 (M.op X0 X1) X2
               have i₂ := b5e856 X0 X1
               grind)
            | (have i₁ := b5e856 (M.op X0 y) x
               have i₂ := b5e856 X0 x
               grind)
            | exact superpose b5e856 b5e856
            | exact resolve b5e856 b5e856
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3392 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 X2) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e856 X0 X2
               have i₂ := b5e856 X0 X1
               grind)
            | (have i₁ := b5e856 X0 x
               have i₂ := b5e856 X0 y
               grind)
            | exact superpose b5e856 b5e856
            | exact resolve b5e856 b5e856
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e856
          have b5e3557 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) y) = (M.op (M.op (M.op X0 X1) X2) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e3381 X0 X1 X2
               have i₂ := b5e493 X0 y
               grind)
            | exact superpose b5e493 b5e3381
            | exact resolve b5e3381 b5e493
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e493 b5e3381
          have b5e5857 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) y) = (M.op y (M.op X3 y)) ∨ (k (M.op X0 X2) y) = (M.op y (M.op X0 X2)) ∨ y = (M.op (M.op X0 X1) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e61 (M.op X0 X1) y X2
               have i₂ := b5e3392 X0 X1 X2
               grind)
            | (have i₁ := b5e61 (M.op X0 X2) y X2
               have i₂ := b5e3392 X0 X1 X2
               grind)
            | exact superpose b5e3392 b5e61
            | (have j0 := b5e61 (M.op X0 X1) y X3
               grind)
            | exact resolve b5e61 b5e3392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e5871 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X0 X1) y) ∨ (k (M.op X0 X2) y) = (M.op y (M.op X0 X2)) ∨ y = (M.op (M.op X0 X1) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e5857 X0 X1 X2 x
               have i₂ := b5e383 y y x
               grind)
            | exact superpose b5e383 b5e5857
            | (have j0 := b5e5857 X0 X1 X2 x
               grind)
            | exact resolve b5e5857 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5857
          have b5e5966 : ∀ X0 X1 X2 : G, (M.op y y) = (k (M.op X0 X2) y) ∨ (M.op y y) = (M.op (M.op X0 X1) y) ∨ y = (M.op (M.op X0 X1) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e5871 X0 X1 X2
               have i₂ := b5e383 y X2 X0
               grind)
            | exact superpose b5e383 b5e5871
            | (have j0 := b5e5871 X0 X1 X2
               grind)
            | exact resolve b5e5871 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5871
          have b5e11945 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e2952 (τ X0)
               have i₂ := b5e28 X0 (τ X0)
               grind)
            | exact superpose b5e28 b5e2952
            | (have j0 := b5e2952 (τ X0)
               grind)
            | exact resolve b5e2952 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e11948 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e11945 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e11945
            | (have j0 := b5e11945 X0
               grind)
            | exact resolve b5e11945 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11945
          have b5e11952 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e11948 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e11948
            | (have j0 := b5e11948 X0
               grind)
            | exact resolve b5e11948 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11948
          have b5e11961 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e11952 (τ X0)
               have i₂ := b5e1563 X0 X0
               grind)
            | exact superpose b5e1563 b5e11952
            | (have j0 := b5e11952 (τ X0)
               grind)
            | exact resolve b5e11952 b5e1563
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11952
          have b5e26456 : ∀ X0 : G, (M.op y y) = (k (M.op y y) (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e578 y X0
               have i₂ := b5e251 X0 y
               grind)
            | exact superpose b5e251 b5e578
            | exact resolve b5e578 b5e251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e26462 : (M.op y y) = (k (M.op y y) (M.op y y)) := by
            first
            | (have i₁ := b5e578 y y
               have i₂ := b5e172 y
               grind)
            | exact superpose b5e172 b5e578
            | exact resolve b5e578 b5e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e172 b5e578
          have b5e28876 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e2952 (M.op y y)
               have i₂ := b5e26456 y
               grind)
            | exact superpose b5e26456 b5e2952
            | (have j0 := b5e2952 (M.op y y)
               grind)
            | exact resolve b5e2952 b5e26456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2952
          have b5e28883 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
          clear b5e28876
          have b5e28953 : ∀ X0 X1 : G, (M.op X0 y) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 y) = (k (M.op X0 X1) X0) ∨ (M.op X0 y) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e1558 (M.op X1 X0) X1
               have i₂ := b5e251 X0 X1
               grind)
            | exact superpose b5e251 b5e1558
            | exact resolve b5e1558 b5e251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e251 b5e1558
          have b5e29210 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X0 X1) X0) ∨ (M.op X0 y) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e28953 X0 X1
               grind)
            | (have r₁ := b5e28953 x x
               have r₂ := b5e383 x x x
               grind)
            | exact resolve b5e28953 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28953
          have b5e29849 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1559 X0 X1
               have i₂ := b5e61 X0 X1 X2
               grind)
            | exact superpose b5e61 b5e1559
            | (have j0 := b5e1559 X2 X0
               have j1 := b5e61 X2 X0 X2
               grind)
            | (have r₁ := b5e1559 (M.op X2 X1) X1
               have r₂ := b5e61 (M.op X2 X1) X1 X2
               grind)
            | (have r₁ := b5e1559 X1 (M.op X2 X1)
               have r₂ := b5e61 (M.op X2 X1) X1 X2
               grind)
            | exact resolve b5e1559 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e29910 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) ≠ (M.op y (M.op X0 X2)) ∨ (k (M.op X0 X2) y) = (M.op y (M.op X0 X2)) ∨ y = (M.op (M.op X0 X1) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1559 (M.op X0 X1) y
               have i₂ := b5e3392 X0 X1 X2
               grind)
            | (have i₁ := b5e1559 (M.op X0 X2) y
               have i₂ := b5e3392 X0 X1 X2
               grind)
            | exact superpose b5e3392 b5e1559
            | (have j0 := b5e1559 (M.op X0 X2) y
               grind)
            | exact resolve b5e1559 b5e3392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1559 b5e3392
          have b5e30024 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e29849 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29849
          have b5e30115 : ∀ X0 X1 X2 : G, (M.op y y) ≠ (M.op (M.op X0 X1) y) ∨ (k (M.op X0 X2) y) = (M.op y (M.op X0 X2)) ∨ y = (M.op (M.op X0 X1) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e29910 X0 X1 X2
               have i₂ := b5e383 y X2 X0
               grind)
            | exact superpose b5e383 b5e29910
            | (have j0 := b5e29910 X0 X1 X2
               grind)
            | exact resolve b5e29910 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29910
          have b5e30171 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e30024 X0 X1 X2
               have j1 := b5e122 X2 X1 X2 X0
               grind)
            | (have r₁ := b5e30024 x X2 X0
               have r₂ := b5e122 X0 x X2 x
               grind)
            | (have r₁ := b5e30024 X1 X1 (M.op X2 x)
               have r₂ := b5e122 (M.op X1 X1) X1 X2 x
               grind)
            | (have r₁ := b5e30024 X0 X1 (M.op X0 (M.op X1 X0))
               have r₂ := b5e122 X0 X1 X2 (M.op X0 (M.op X1 X0))
               grind)
            | exact resolve b5e30024 b5e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e122 b5e30024
          have b5e30258 : ∀ X0 X1 X2 : G, (M.op y y) = (k (M.op X0 X2) y) ∨ (M.op y y) ≠ (M.op (M.op X0 X1) y) ∨ y = (M.op (M.op X0 X1) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e30115 X0 X1 X2
               have i₂ := b5e383 y X2 X0
               grind)
            | exact superpose b5e383 b5e30115
            | (have j0 := b5e30115 X0 X1 X2
               grind)
            | exact resolve b5e30115 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30115
          have b5e30314 : ∀ X0 X2 : G, (M.op X0 y) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X2
            first
            | (have i₁ := b5e30171 X0 x X2
               have i₂ := b5e383 X0 X0 x
               grind)
            | exact superpose b5e383 b5e30171
            | (have j0 := b5e30171 X0 x X2
               grind)
            | exact resolve b5e30171 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30171
          have b5e30386 : ∀ X0 X1 X2 : G, (M.op y y) = (k (M.op X0 X2) y) ∨ y = (M.op (M.op X0 X1) y) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e30258 X0 X1 X2
               have j1 := b5e5966 X0 X1 X2
               grind)
            | (have r₁ := b5e30258 X0 X1 X2
               have r₂ := b5e5966 X0 X1 X2
               grind)
            | exact resolve b5e30258 b5e5966
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5966 b5e30258
          have b5e30435 : ∀ X0 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X2
            first
            | (have j0 := b5e30314 X0 X2
               have j1 := b5e1753 X2 X0
               grind)
            | (have r₁ := b5e30314 x X2
               have r₂ := b5e1753 X0 x
               grind)
            | (have r₁ := b5e30314 y y
               have r₂ := b5e1753 X0 y
               grind)
            | exact resolve b5e30314 b5e1753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1753 b5e30314
          have b5e33978 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e89 X1 X0
               have i₂ := b5e30435 X0 (σ X1)
               grind)
            | exact superpose b5e30435 b5e89
            | (have j1 := b5e30435 X0 (σ X1)
               grind)
            | exact resolve b5e89 b5e30435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89 b5e30435
          have b5e47531 : (M.op (σ (M.op y y)) y) = (k (σ (M.op y y)) (σ (M.op y y))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) y) := by
            first
            | (have i₁ := b5e29210 (σ (M.op y y)) (σ (M.op y y))
               have i₂ := b5e28883
               grind)
            | exact superpose b5e28883 b5e29210
            | (have j0 := b5e29210 (σ (M.op y y)) x
               grind)
            | exact resolve b5e29210 b5e28883
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28883
          have b5e47537 : (σ (k (M.op y y) (M.op y y))) = (M.op (σ (M.op y y)) y) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) y) := by
            first
            | (have i₁ := b5e47531
               have i₂ := b5e19 (M.op y y) (M.op y y)
               grind)
            | exact superpose b5e19 b5e47531
            | exact resolve b5e47531 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47531
          have b5e47594 : (σ (M.op y y)) = (M.op (σ (M.op y y)) y) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) y) := by
            first
            | (have i₁ := b5e47537
               have i₂ := b5e26462
               grind)
            | exact superpose b5e26462 b5e47537
            | exact resolve b5e47537 b5e26462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47537
          have b5e47595 : (σ (M.op y y)) = (M.op (σ (M.op y y)) y) := by grind
          clear b5e47594
          have b5e57823 : (τ (M.op y y)) ≠ (τ (M.op y y)) ∨ (τ (M.op y y)) = (M.op (τ (M.op y y)) (τ (M.op y y))) := by
            first
            | (have i₁ := b5e11961 (M.op y y)
               have i₂ := b5e26456 y
               grind)
            | exact superpose b5e26456 b5e11961
            | (have j0 := b5e11961 (M.op y y)
               grind)
            | exact resolve b5e11961 b5e26456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11961 b5e26456
          have b5e57835 : (τ (M.op y y)) = (M.op (τ (M.op y y)) (τ (M.op y y))) := by grind
          clear b5e57823
          have b5e58155 : (M.op (τ (M.op y y)) y) = (k (τ (M.op y y)) (τ (M.op y y))) ∨ (τ (M.op y y)) = (M.op (τ (M.op y y)) y) := by
            first
            | (have i₁ := b5e29210 (τ (M.op y y)) (τ (M.op y y))
               have i₂ := b5e57835
               grind)
            | exact superpose b5e57835 b5e29210
            | (have j0 := b5e29210 (τ (M.op y y)) x
               grind)
            | exact resolve b5e29210 b5e57835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29210 b5e57835
          have b5e58160 : (τ (k (M.op y y) (M.op y y))) = (M.op (τ (M.op y y)) y) ∨ (τ (M.op y y)) = (M.op (τ (M.op y y)) y) := by
            first
            | (have i₁ := b5e58155
               have i₂ := b5e1563 (M.op y y) (M.op y y)
               grind)
            | exact superpose b5e1563 b5e58155
            | exact resolve b5e58155 b5e1563
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58155
          have b5e58221 : (τ (M.op y y)) = (M.op (τ (M.op y y)) y) ∨ (τ (M.op y y)) = (M.op (τ (M.op y y)) y) := by
            first
            | (have i₁ := b5e58160
               have i₂ := b5e26462
               grind)
            | exact superpose b5e26462 b5e58160
            | exact resolve b5e58160 b5e26462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26462 b5e58160
          have b5e58222 : (τ (M.op y y)) = (M.op (τ (M.op y y)) y) := by grind
          clear b5e58221
          have b5e78079 : ∀ X0 X2 : G, (M.op y y) = (k (M.op X0 X2) y) ∨ y = (M.op y y) := by
            intro X0 X2
            first
            | (have i₁ := b5e506 X0 x y
               have i₂ := b5e30386 X0 x X2
               grind)
            | exact superpose b5e30386 b5e506
            | (have j1 := b5e30386 X0 x X2
               grind)
            | exact resolve b5e506 b5e30386
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e506 b5e30386
          have b5e80188 : (M.op y y) = (k (τ (M.op y y)) y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e78079 (τ (M.op y y)) y
               have i₂ := b5e58222
               grind)
            | exact superpose b5e58222 b5e78079
            | exact resolve b5e78079 b5e58222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58222 b5e78079
          have b5e83639 : (σ (M.op y y)) = (k (M.op y y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e27 (M.op y y) y
               have i₂ := b5e80188
               grind)
            | exact superpose b5e80188 b5e27
            | exact resolve b5e27 b5e80188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e80188
          have b5e86603 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e33978 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e33978
            | exact resolve b5e33978 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33978
          have b5e86765 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e86603 X0 X1
               have i₂ := b5e1563 X1 X0
               grind)
            | exact superpose b5e1563 b5e86603
            | (have j0 := b5e86603 X0 X1
               grind)
            | exact resolve b5e86603 b5e1563
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1563 b5e86603
          have b5e144693 : (τ (σ (M.op y y))) = (τ (M.op (σ y) (M.op y y))) ∨ (σ y) = (M.op (M.op y y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e86765 (M.op y y) (σ y)
               have i₂ := b5e83639
               grind)
            | exact superpose b5e83639 b5e86765
            | (have j0 := b5e86765 (M.op y y) (σ y)
               grind)
            | exact resolve b5e86765 b5e83639
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83639 b5e86765
          have b5e144696 : (τ (M.op (σ y) y)) = (τ (σ (M.op y y))) ∨ (σ y) = (M.op (M.op y y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e144693
               have i₂ := b5e383 (σ y) y y
               grind)
            | exact superpose b5e383 b5e144693
            | exact resolve b5e144693 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e383 b5e144693
          have b5e144727 : (M.op y y) = (τ (M.op (σ y) y)) ∨ (σ y) = (M.op (M.op y y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e144696
               have i₂ := b5e14 (M.op y y)
               grind)
            | exact superpose b5e14 b5e144696
            | exact resolve b5e144696 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e144696
          have b5e144751 : (M.op y y) = (τ (σ x)) ∨ (σ y) = (M.op (M.op y y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e144727
               have i₂ := b5e1935
               grind)
            | exact superpose b5e1935 b5e144727
            | exact resolve b5e144727 b5e1935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e144727
          have b5e144754 : x = (M.op y y) ∨ (σ y) = (M.op (M.op y y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e144751
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e144751
            | exact resolve b5e144751 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e144751
          have b5e144755 : (σ y) = (M.op (M.op y y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b5e144754
               have r₂ := b5e21
               grind)
            | exact resolve b5e144754 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e144754
          have b5e147515 : (M.op (M.op y y) y) = (M.op (σ y) y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e3557 y y (σ y)
               have i₂ := b5e144755
               grind)
            | exact superpose b5e144755 b5e3557
            | exact resolve b5e3557 b5e144755
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3557
          have b5e147520 : (σ x) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e147515
               have i₂ := b5e1935
               grind)
            | exact superpose b5e1935 b5e147515
            | exact resolve b5e147515 b5e1935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e147515
          have b5e147626 : (σ x) = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e147520
               have i₂ := b5e71
               grind)
            | exact superpose b5e71 b5e147520
            | exact resolve b5e147520 b5e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71 b5e147520
          have b5e149688 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (σ x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e144755
               have i₂ := b5e147626
               grind)
            | exact superpose b5e147626 b5e144755
            | exact resolve b5e144755 b5e147626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e144755
          have b5e149851 : y ≠ (σ x) ∨ y = (M.op y y) := by grind
          clear b5e147626
          have b5e149936 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b5e149688
               have r₂ := b5e149851
               grind)
            | exact resolve b5e149688 b5e149851
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e149688 b5e149851
          have b5e149976 : y = (M.op y y) := by
            first
            | (have r₁ := b5e149936
               have r₂ := b5e24
               grind)
            | exact resolve b5e149936 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e149936
          have b5e150490 : (σ y) = (M.op (σ y) y) := by
            first
            | (have i₁ := b5e47595
               have i₂ := b5e149976
               grind)
            | exact superpose b5e149976 b5e47595
            | exact resolve b5e47595 b5e149976
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47595 b5e149976
          have b5e153513 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1935
               have i₂ := b5e150490
               grind)
            | exact superpose b5e150490 b5e1935
            | exact resolve b5e1935 b5e150490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1935 b5e150490
          have b5e153838 : False := by grind
          exact b5e153838
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ y) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b6e38 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e37
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e37
          | exact resolve b6e37 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e51 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e38
             grind)
          | exact superpose b6e38 b6e19
          | exact resolve b6e19 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b6e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e70 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e26 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e26
          | exact resolve b6e26 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e81 : (σ (k x y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e70
             have i₂ := b6e38
             grind)
          | exact superpose b6e38 b6e70
          | exact resolve b6e70 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38 b6e70
        have b6e1385 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k x y) = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e51
             have i₂ := b6e62 x y
             grind)
          | exact superpose b6e62 b6e51
          | (have j1 := b6e62 x y
             grind)
          | exact resolve b6e51 b6e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e1388 : (k x y) = (M.op y x) ∨ y = (M.op x y) := by grind
        clear b6e1385
        have b6e1390 : (k x y) = (M.op y x) := by
          first
          | (have r₁ := b6e1388
             have r₂ := b6e21
             grind)
          | exact resolve b6e1388 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1388
        have b6e3105 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e60 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e60
          | exact resolve b6e60 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e3224 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e3105
        have b6e4689 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e3224
             grind)
          | exact superpose b6e3224 b6e13
          | exact resolve b6e13 b6e3224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3224
        have b6e4704 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e4689
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e4689
          | exact resolve b6e4689 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4689
        have b6e4712 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e62 y y
             have i₂ := b6e4704
             grind)
          | exact superpose b6e4704 b6e62
          | (have j0 := b6e62 y y
             grind)
          | exact resolve b6e62 b6e4704
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e4713 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e4712
        have b6e4717 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e4713
             have r₂ := b6e20
             grind)
          | exact resolve b6e4713 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4713
        have b6e4810 : (M.op y y) = (k y y) ∨ (σ x) = (σ y) := by grind
        clear b6e4717
        have b6e6404 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e4704
             have i₂ := b6e4810
             grind)
          | exact superpose b6e4810 b6e4704
          | exact resolve b6e4704 b6e4810
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4704 b6e4810
        have b6e6407 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e6404
        have b6e6409 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e6407
             have r₂ := b6e20
             grind)
          | exact resolve b6e6407 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6407
        have b6e7327 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e6409
             grind)
          | exact superpose b6e6409 b6e19
          | exact resolve b6e19 b6e6409
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e7331 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e81
             have i₂ := b6e6409
             grind)
          | exact superpose b6e6409 b6e81
          | exact resolve b6e81 b6e6409
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e7335 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e6409
             grind)
          | exact superpose b6e6409 b6e13
          | exact resolve b6e13 b6e6409
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e7352 : x = y := by
          first
          | (have i₁ := b6e7335
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e7335
          | exact resolve b6e7335 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7335
        have b6e7356 : (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e7331
             have i₂ := b6e1390
             grind)
          | exact superpose b6e1390 b6e7331
          | exact resolve b6e7331 b6e1390
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1390 b6e7331
        have b6e7360 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e7327
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e7327
          | exact resolve b6e7327 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7327
        have b6e7364 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e7356
             have i₂ := b6e7352
             grind)
          | exact superpose b6e7352 b6e7356
          | exact resolve b6e7356 b6e7352
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7356
        have b6e7367 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e7360
             have i₂ := b6e6409
             grind)
          | exact superpose b6e6409 b6e7360
          | exact resolve b6e7360 b6e6409
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7360
        have b6e7371 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e7364
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e7364
          | exact resolve b6e7364 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7364
        have b6e7374 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e7367
             have i₂ := b6e7352
             grind)
          | exact superpose b6e7352 b6e7367
          | exact resolve b6e7367 b6e7352
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7352 b6e7367
        have b6e7375 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e7371
             have i₂ := b6e6409
             grind)
          | exact superpose b6e6409 b6e7371
          | exact resolve b6e7371 b6e6409
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6409 b6e7371
        have b6e7378 : False := by grind
        exact b6e7378
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e27 X0 X1
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e33 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
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
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 X0 (M.op X3 X1)
               have i₂ := b7e13 X0 X3 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op X0 X2) X0
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 (M.op X3 X1))) = (M.op (M.op (M.op X0 X1) X0) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X2 (M.op X3 X1)
               have i₂ := b7e13 X0 X3 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 X0)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X0 X2) X3 X0
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e13 X0 X3 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b7e58 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e59 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X2 X1) ∨ (M.op (M.op X2 X1) (M.op X2 X1)) = X0 ∨ (k X0 (M.op X2 X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 X0 (M.op X2 X1)
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e17
            | (have j0 := b7e17 X0 (M.op X2 X1)
               grind)
            | (have r₁ := b7e17 X0 (M.op (M.op X0 X0) X0)
               have r₂ := b7e13 X0 (M.op X0 X0) X0
               grind)
            | exact resolve b7e17 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e61 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
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
          have b7e76 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b7e79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e81 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 X1
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e18 (M.op X0 X2) X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X0 X1
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e87 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
          have b7e88 : x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e87
               have r₂ := b7e21
               grind)
            | exact resolve b7e87 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e90 : x = (M.op y x) := by
            first
            | (have r₁ := b7e88
               have r₂ := b7e22
               grind)
            | exact resolve b7e88 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e97 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (σ y)
               have i₂ := b7e33 X0
               grind)
            | exact superpose b7e33 b7e13
            | exact resolve b7e13 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e103 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 x
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e13
            | exact resolve b7e13 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e122 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (M.op X2 X3)) ∨ (M.op X3 X0) = (k X0 X3) ∨ (M.op X0 X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e39 X1 X2 X3 X3
               have i₂ := b7e18 X0 X3
               grind)
            | (have i₁ := b7e39 X0 X1 X2 X3
               have i₂ := b7e18 (M.op X3 X2) X1
               grind)
            | exact superpose b7e18 b7e39
            | (have j1 := b7e18 X0 X3
               grind)
            | exact resolve b7e39 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e123 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X4 X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e39 X3 X4 X0 (M.op X0 X2)
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e39
            | exact resolve b7e39 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e124 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e39 X1 X2 X0 (M.op X0 (σ y))
               have i₂ := b7e33 X0
               grind)
            | exact superpose b7e33 b7e39
            | exact resolve b7e39 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e151 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e124 X0 X1 X2
               have i₂ := b7e97 X1 X0
               grind)
            | exact superpose b7e97 b7e124
            | exact resolve b7e124 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97 b7e124
          have b7e209 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (M.op X4 (M.op X2 X3))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e39 X0 X1 (M.op X2 X3) X4
               have i₂ := b7e35 X1 X2 X3 X0
               grind)
            | exact superpose b7e35 b7e39
            | exact resolve b7e39 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e222 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e209 X0 X1 x x x
               have i₂ := b7e151 (M.op x x) X0 x
               grind)
            | exact superpose b7e151 b7e209
            | exact resolve b7e209 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e209
          have b7e305 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b7e103 y
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e103
            | exact resolve b7e103 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103
          have b7e324 : x = (M.op x y) := by
            first
            | (have i₁ := b7e305
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e305
            | exact resolve b7e305 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e305
          have b7e523 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e39 X0 X1 y x
               have i₂ := b7e324
               grind)
            | exact superpose b7e324 b7e39
            | exact resolve b7e39 b7e324
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e324
          have b7e524 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e523 X0 x
               have i₂ := b7e151 y X0 x
               grind)
            | exact superpose b7e151 b7e523
            | exact resolve b7e523 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e523
          have b7e574 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X2)) (M.op X0 X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e37 (M.op X0 X2) X0 X3 X4
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e37
            | exact resolve b7e37 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e575 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (M.op X1 (M.op X2 X0))) = (M.op (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) (M.op X0 (σ y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e37 (M.op X0 (σ y)) X0 X1 X2
               have i₂ := b7e33 X0
               grind)
            | exact superpose b7e33 b7e37
            | exact resolve b7e37 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e618 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1)) (M.op (M.op X5 X1) X5)) = (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e34 X5 X1 (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1)) X0
               have i₂ := b7e37 (M.op X0 X1) X4 X2 X3
               grind)
            | exact superpose b7e37 b7e34
            | exact resolve b7e34 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e621 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) = (M.op (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1)) (M.op X5 X1)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e39 (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1)) X0 X1 X5
               have i₂ := b7e37 (M.op X0 X1) X4 X2 X3
               grind)
            | exact superpose b7e37 b7e39
            | exact resolve b7e39 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e623 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X0 (M.op X1 X2))) = (M.op (M.op (σ y) (M.op X0 (M.op X1 X2))) (M.op (M.op (σ y) X2) (σ y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e33 (M.op (M.op (σ y) X1) (σ y))
               have i₂ := b7e37 (σ y) X1 X2 x
               grind)
            | exact superpose b7e37 b7e33
            | exact resolve b7e33 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e37
          have b7e626 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X0 (M.op X1 X2))) = (M.op (M.op (σ y) (M.op X0 (M.op X1 X2))) (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e623 X0 X1 X2
               have i₂ := b7e151 (σ y) (M.op (σ y) (M.op X0 (M.op X1 X2))) (M.op (σ y) X2)
               grind)
            | exact superpose b7e151 b7e623
            | exact resolve b7e623 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e623
          have b7e628 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) = (M.op (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1)) (σ y)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e621 X0 X1 X2 X3 X4 x
               have i₂ := b7e151 X1 (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1)) x
               grind)
            | exact superpose b7e151 b7e621
            | exact resolve b7e621 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e621
          have b7e631 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) (σ y)) = (M.op (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1)) (M.op (M.op X5 X1) X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e618 X0 X1 X2 X3 X4 X5
               have i₂ := b7e151 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) (M.op (M.op X0 X1) X4)
               grind)
            | exact superpose b7e151 b7e618
            | exact resolve b7e618 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e618
          have b7e663 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (M.op X1 (M.op X2 X0))) = (M.op (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e575 X0 X1 X2
               have i₂ := b7e151 (σ y) (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) X0
               grind)
            | exact superpose b7e151 b7e575
            | exact resolve b7e575 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e575
          have b7e664 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X2)) (σ y)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e574 X0 X1 X2 X3 X4
               have i₂ := b7e151 X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X2)) X0
               grind)
            | exact superpose b7e151 b7e574
            | exact resolve b7e574 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e574
          have b7e706 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X0 (M.op X1 X2))) = (M.op (M.op (σ y) (M.op X0 (M.op X1 X2))) x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e626 X0 X1 X2
               have i₂ := b7e524 (M.op (σ y) (M.op X0 (M.op X1 X2)))
               grind)
            | exact superpose b7e524 b7e626
            | exact resolve b7e626 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e626
          have b7e708 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) = (M.op (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1)) x) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e628 X0 X1 X2 X3 X4
               have i₂ := b7e524 (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1))
               grind)
            | exact superpose b7e524 b7e628
            | exact resolve b7e628 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e628
          have b7e710 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) (σ y)) = (M.op (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1)) (σ y)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e631 X0 X1 X2 X3 X4 x
               have i₂ := b7e151 x (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1)) (M.op x X1)
               grind)
            | exact superpose b7e151 b7e631
            | exact resolve b7e631 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e631
          have b7e727 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (M.op X1 (M.op X2 X0))) = (M.op (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e663 X0 X1 X2
               have i₂ := b7e524 (M.op (M.op X0 (σ y)) (M.op X0 (σ y)))
               grind)
            | exact superpose b7e524 b7e663
            | exact resolve b7e663 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e663
          have b7e728 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X2)) x) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e664 X0 X1 X2 X3 X4
               have i₂ := b7e524 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X2))
               grind)
            | exact superpose b7e524 b7e664
            | exact resolve b7e664 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e664
          have b7e736 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) x) := by
            first
            | (have i₁ := b7e706 x x x
               have i₂ := b7e151 (M.op x x) (σ y) x
               grind)
            | exact superpose b7e151 b7e706
            | exact resolve b7e706 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e706
          have b7e737 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) = (M.op (M.op (M.op (M.op X0 X1) X4) (σ y)) x) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e708 X0 X1 X2 X3 X4
               have i₂ := b7e151 X1 (M.op (M.op X0 X1) X4) X0
               grind)
            | exact superpose b7e151 b7e708
            | exact resolve b7e708 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e708
          have b7e739 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) (σ y)) = (M.op (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1)) x) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e710 X0 X1 X2 X3 X4
               have i₂ := b7e524 (M.op (M.op (M.op X0 X1) X4) (M.op X0 X1))
               grind)
            | exact superpose b7e524 b7e710
            | exact resolve b7e710 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e710
          have b7e752 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (M.op X1 (M.op X2 X0))) = (M.op (M.op (M.op X0 (σ y)) (σ y)) x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e727 X0 X1 X2
               have i₂ := b7e151 (σ y) (M.op X0 (σ y)) X0
               grind)
            | exact superpose b7e151 b7e727
            | exact resolve b7e727 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e727
          have b7e753 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op X0 (M.op X1 X2)) (σ y)) x) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e728 X0 X1 X2 X3 X4
               have i₂ := b7e151 X2 (M.op X0 (M.op X1 X2)) X0
               grind)
            | exact superpose b7e151 b7e728
            | exact resolve b7e728 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e728
          have b7e756 : (M.op (σ y) x) = (M.op (M.op (σ y) x) x) := by
            first
            | (have i₁ := b7e736
               have i₂ := b7e524 (σ y)
               grind)
            | exact superpose b7e524 b7e736
            | exact resolve b7e736 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e736
          have b7e757 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) = (M.op (M.op (M.op (M.op X0 X1) X4) x) x) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e737 X0 X1 X2 X3 X4
               have i₂ := b7e524 (M.op (M.op X0 X1) X4)
               grind)
            | exact superpose b7e524 b7e737
            | exact resolve b7e737 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e737
          have b7e759 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) (σ y)) = (M.op (M.op (M.op (M.op X0 X1) X4) (σ y)) x) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e739 X0 X1 X2 X3 X4
               have i₂ := b7e151 X1 (M.op (M.op X0 X1) X4) X0
               grind)
            | exact superpose b7e151 b7e739
            | exact resolve b7e739 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e739
          have b7e771 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (M.op X1 (M.op X2 X0))) = (M.op (M.op (M.op X0 (σ y)) x) x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e752 X0 X1 X2
               have i₂ := b7e524 (M.op X0 (σ y))
               grind)
            | exact superpose b7e524 b7e752
            | exact resolve b7e752 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e752
          have b7e772 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op X0 (M.op X1 X2)) x) x) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e753 X0 X1 X2 X3 X4
               have i₂ := b7e524 (M.op X0 (M.op X1 X2))
               grind)
            | exact superpose b7e524 b7e753
            | exact resolve b7e753 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e753
          have b7e775 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op (M.op (M.op X0 X1) X4) x) x) := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e757 X0 X1 x x X4
               have i₂ := b7e151 (M.op x X4) (M.op X0 X1) x
               grind)
            | exact superpose b7e151 b7e757
            | exact resolve b7e757 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e757
          have b7e777 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) (σ y)) = (M.op (M.op (M.op (M.op X0 X1) X4) x) x) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e759 X0 X1 X2 X3 X4
               have i₂ := b7e524 (M.op (M.op X0 X1) X4)
               grind)
            | exact superpose b7e524 b7e759
            | exact resolve b7e759 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e759
          have b7e788 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op X1 (M.op X2 X0))) = (M.op (M.op (M.op X0 x) x) x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e771 X0 X1 X2
               have i₂ := b7e524 X0
               grind)
            | exact superpose b7e524 b7e771
            | exact resolve b7e771 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e771
          have b7e789 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op X0 (σ y)) x) x) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b7e772 X0 x X2 X3 X4
               have i₂ := b7e151 X2 X0 x
               grind)
            | exact superpose b7e151 b7e772
            | exact resolve b7e772 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e772
          have b7e791 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X4) x) x) = (M.op (M.op X0 X1) x) := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e775 X0 X1 X4
               have i₂ := b7e524 (M.op X0 X1)
               grind)
            | exact superpose b7e524 b7e775
            | exact resolve b7e775 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e775
          have b7e793 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X4) x) x) = (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) x) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e777 X0 X1 X2 X3 X4
               have i₂ := b7e524 (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4)))
               grind)
            | exact superpose b7e524 b7e777
            | exact resolve b7e777 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e777
          have b7e804 : ∀ X0 : G, (M.op (M.op X0 x) (σ y)) = (M.op (M.op (M.op X0 x) x) x) := by
            intro X0
            first
            | (have i₁ := b7e788 X0 x x
               have i₂ := b7e151 (M.op x X0) (M.op X0 x) x
               grind)
            | exact superpose b7e151 b7e788
            | exact resolve b7e788 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e788
          have b7e805 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op X0 x) x) x) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b7e789 X0 X2 X3 X4
               have i₂ := b7e524 X0
               grind)
            | exact superpose b7e524 b7e789
            | exact resolve b7e789 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e789
          have b7e807 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X4) x) x) = (M.op (M.op (M.op X0 X1) (σ y)) x) := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e793 X0 X1 x x X4
               have i₂ := b7e151 (M.op x X4) (M.op X0 X1) x
               grind)
            | exact superpose b7e151 b7e793
            | exact resolve b7e793 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e793
          have b7e813 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op (M.op (M.op X0 x) x) x) := by
            intro X0
            first
            | (have i₁ := b7e804 X0
               have i₂ := b7e524 (M.op X0 x)
               grind)
            | exact superpose b7e524 b7e804
            | exact resolve b7e804 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e804
          have b7e814 : ∀ X0 X2 : G, (M.op (M.op X0 X2) (σ y)) = (M.op (M.op (M.op X0 x) x) x) := by
            intro X0 X2
            first
            | (have i₁ := b7e805 X0 X2 x x
               have i₂ := b7e151 (M.op x X0) (M.op X0 X2) x
               grind)
            | exact superpose b7e151 b7e805
            | exact resolve b7e805 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e805
          have b7e816 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X4) x) x) = (M.op (M.op (M.op X0 X1) x) x) := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e807 X0 X1 X4
               have i₂ := b7e524 (M.op X0 X1)
               grind)
            | exact superpose b7e524 b7e807
            | exact resolve b7e807 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e807
          have b7e820 : ∀ X0 X2 : G, (M.op (M.op X0 X2) (σ y)) = (M.op (M.op X0 x) x) := by
            intro X0 X2
            first
            | (have i₁ := b7e814 X0 X2
               have i₂ := b7e813 X0
               grind)
            | exact superpose b7e813 b7e814
            | exact resolve b7e814 b7e813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e813 b7e814
          have b7e822 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op (M.op (M.op X0 X1) x) x) := by
            intro X0 X1
            first
            | (have i₁ := b7e816 X0 X1 x
               have i₂ := b7e791 X0 X1 x
               grind)
            | exact superpose b7e791 b7e816
            | exact resolve b7e816 b7e791
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e791 b7e816
          have b7e826 : ∀ X0 X2 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X2) x) := by
            intro X0 X2
            first
            | (have i₁ := b7e820 X0 X2
               have i₂ := b7e524 (M.op X0 X2)
               grind)
            | exact superpose b7e524 b7e820
            | exact resolve b7e820 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e820
          have b7e844 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X5 X3)) (M.op (M.op X0 X1) X3)) = (M.op (M.op (M.op X0 X1) X3) (M.op (M.op X0 X1) (M.op X2 X0))) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b7e38 (M.op X0 X1) X5 X3 (M.op X0 (M.op x X1))
               have i₂ := b7e38 X0 x X1 X2
               grind)
            | exact superpose b7e38 b7e38
            | exact resolve b7e38 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e1030 : ∀ X0 X1 X3 X5 : G, (M.op (M.op (M.op X0 X1) X3) (σ y)) = (M.op (M.op (M.op X0 X1) (M.op X5 X3)) (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X3 X5
            first
            | (have i₁ := b7e844 X0 X1 x X3 X5
               have i₂ := b7e151 (M.op x X0) (M.op (M.op X0 X1) X3) (M.op X0 X1)
               grind)
            | exact superpose b7e151 b7e844
            | exact resolve b7e844 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e844
          have b7e1115 : ∀ X0 X1 X3 X5 : G, (M.op (M.op (M.op X0 X1) X3) (σ y)) = (M.op (M.op (M.op X0 X1) (M.op X5 X3)) (σ y)) := by
            intro X0 X1 X3 X5
            first
            | (have i₁ := b7e1030 X0 X1 X3 X5
               have i₂ := b7e151 X3 (M.op (M.op X0 X1) (M.op X5 X3)) (M.op X0 X1)
               grind)
            | exact superpose b7e151 b7e1030
            | exact resolve b7e1030 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1030
          have b7e1198 : ∀ X0 X1 X3 X5 : G, (M.op (M.op (M.op X0 X1) X3) (σ y)) = (M.op (M.op (M.op X0 X1) (M.op X5 X3)) x) := by
            intro X0 X1 X3 X5
            first
            | (have i₁ := b7e1115 X0 X1 X3 X5
               have i₂ := b7e524 (M.op (M.op X0 X1) (M.op X5 X3))
               grind)
            | exact superpose b7e524 b7e1115
            | exact resolve b7e1115 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1115
          have b7e1280 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X3) (σ y)) = (M.op (M.op (M.op X0 X1) x) x) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e1198 X0 X1 X3 x
               have i₂ := b7e826 (M.op X0 X1) (M.op x X3)
               grind)
            | exact superpose b7e826 b7e1198
            | exact resolve b7e1198 b7e826
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1198
          have b7e1356 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X3) (σ y)) = (M.op (M.op X0 X1) x) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e1280 X0 X1 X3
               have i₂ := b7e822 X0 X1
               grind)
            | exact superpose b7e822 b7e1280
            | exact resolve b7e1280 b7e822
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e822 b7e1280
          have b7e1408 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) x) = (M.op (M.op (M.op X0 X1) X3) x) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e1356 X0 X1 X3
               have i₂ := b7e524 (M.op (M.op X0 X1) X3)
               grind)
            | exact superpose b7e524 b7e1356
            | exact resolve b7e1356 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1356
          have b7e1465 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e79 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e1526 : (M.op (M.op (σ y) x) (σ y)) = (k (M.op (σ y) x) (σ y)) := by grind
          have b7e1554 : (M.op (M.op (σ y) x) x) = (k (M.op (σ y) x) (σ y)) := by
            first
            | (have i₁ := b7e1526
               have i₂ := b7e524 (M.op (σ y) x)
               grind)
            | exact superpose b7e524 b7e1526
            | exact resolve b7e1526 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1526
          have b7e1574 : (M.op (σ y) x) = (k (M.op (σ y) x) (σ y)) := by
            first
            | (have i₁ := b7e1554
               have i₂ := b7e756
               grind)
            | exact superpose b7e756 b7e1554
            | exact resolve b7e1554 b7e756
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e756 b7e1554
          have b7e1717 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e81 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1720 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e1717 X0 X1 x
               have i₂ := b7e151 X1 X1 x
               grind)
            | exact superpose b7e151 b7e1717
            | (have j0 := b7e1717 X0 X1 x
               grind)
            | exact resolve b7e1717 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1717
          have b7e1813 : ∀ X0 X1 : G, (M.op X1 x) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e1720 X0 X1
               have i₂ := b7e524 X1
               grind)
            | exact superpose b7e524 b7e1720
            | (have j0 := b7e1720 X0 X1
               grind)
            | exact resolve b7e1720 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1720
          have b7e2754 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X2 (M.op X1 (M.op X3 X4))) X2) ∨ (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X2 ∨ (k X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e59 X0 (M.op X0 (M.op X1 X2)) X3
               have i₂ := b7e35 X0 X1 X2 X3
               grind)
            | exact superpose b7e35 b7e59
            | (have j0 := b7e59 X2 X0 (M.op X0 X1)
               grind)
            | exact resolve b7e59 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e59
          have b7e2779 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X2 (σ y)) ∨ (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X2 ∨ (k X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e2754 X0 X1 X2 x x
               have i₂ := b7e222 X2 (M.op X1 (M.op x x))
               grind)
            | exact superpose b7e222 b7e2754
            | (have j0 := b7e2754 X0 X1 X2 x x
               grind)
            | (have r₁ := b7e2754 (M.op (σ y) (M.op X1 (M.op x x))) X1 (σ y) x x
               have r₂ := b7e222 (M.op (σ y) (M.op X1 (M.op x x))) X1
               grind)
            | (have r₁ := b7e2754 (σ y) X1 (M.op (σ y) X1) x x
               have r₂ := b7e222 (M.op (σ y) X1) (M.op X1 (M.op x x))
               grind)
            | exact resolve b7e2754 b7e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2754
          have b7e2837 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X2 x) ∨ (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X2 ∨ (k X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e2779 X0 X1 X2
               have i₂ := b7e524 X2
               grind)
            | exact superpose b7e524 b7e2779
            | (have j0 := b7e2779 X0 X1 X2
               grind)
            | (have r₁ := b7e2779 x X1 (M.op x X1)
               have r₂ := b7e524 (M.op x X1)
               grind)
            | exact resolve b7e2779 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2779
          have b7e2895 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) ≠ (M.op X2 x) ∨ (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X2 ∨ (k X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e2837 X0 X1 X2
               have i₂ := b7e222 X0 X1
               grind)
            | exact superpose b7e222 b7e2837
            | (have j0 := b7e2837 X0 X1 X2
               grind)
            | exact resolve b7e2837 b7e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2837
          have b7e2949 : ∀ X0 X1 X2 : G, (M.op X0 x) ≠ (M.op X2 x) ∨ (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X2 ∨ (k X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e2895 X0 X1 X2
               have i₂ := b7e524 X0
               grind)
            | exact superpose b7e524 b7e2895
            | (have j0 := b7e2895 X0 X1 X2
               grind)
            | (have r₁ := b7e2895 X0 X1 X0
               have r₂ := b7e524 X0
               grind)
            | exact resolve b7e2895 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2895
          have b7e2995 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (σ y)) = X2 ∨ (M.op X0 x) ≠ (M.op X2 x) ∨ (k X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e2949 X0 X1 X2
               have i₂ := b7e151 X0 (M.op (M.op X0 X1) X0) (M.op X0 X1)
               grind)
            | exact superpose b7e151 b7e2949
            | (have j0 := b7e2949 X0 X1 X2
               grind)
            | exact resolve b7e2949 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2949
          have b7e3035 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) x) = X2 ∨ (M.op X0 x) ≠ (M.op X2 x) ∨ (k X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e2995 X0 X1 X2
               have i₂ := b7e524 (M.op (M.op X0 X1) X0)
               grind)
            | exact superpose b7e524 b7e2995
            | (have j0 := b7e2995 X0 X1 X2
               grind)
            | exact resolve b7e2995 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2995
          have b7e3068 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) x) = X2 ∨ (M.op X0 x) ≠ (M.op X2 x) ∨ (k X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e3035 X0 X1 X2
               have i₂ := b7e1408 X0 X1 X0
               grind)
            | exact superpose b7e1408 b7e3035
            | (have j0 := b7e3035 X0 X1 X2
               grind)
            | (have r₁ := b7e3035 (M.op X0 X1) X1 (M.op (M.op X0 X1) x)
               have r₂ := b7e1408 X0 X1 x
               grind)
            | (have r₁ := b7e3035 (M.op (M.op X0 X1) x) X1 (M.op X0 X1)
               have r₂ := b7e1408 X0 X1 x
               grind)
            | exact resolve b7e3035 b7e1408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3035
          have b7e3098 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (σ y))) = X2 ∨ (M.op (M.op X0 X1) x) = X2 ∨ (M.op X0 x) ≠ (M.op X2 x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e3068 X0 X1 X2
               have i₂ := b7e222 X0 X1
               grind)
            | exact superpose b7e222 b7e3068
            | (have j0 := b7e3068 X0 X1 X2
               grind)
            | exact resolve b7e3068 b7e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3068
          have b7e3126 : ∀ X0 X1 X2 : G, (M.op X0 x) ≠ (M.op X2 x) ∨ (M.op (M.op X0 X1) x) = X2 ∨ (k X2 (M.op X0 x)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e3098 X0 X1 X2
               have i₂ := b7e524 X0
               grind)
            | exact superpose b7e524 b7e3098
            | (have j0 := b7e3098 X0 X1 X2
               grind)
            | exact resolve b7e3098 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3098
          have b7e3323 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e76 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e3324 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e3323 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3323
          have b7e6551 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            grind
          clear b7e123
          have b7e6629 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) (σ y)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e6551 X0 X1 X2 X3
               have i₂ := b7e151 X1 (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) X0
               grind)
            | exact superpose b7e151 b7e6551
            | exact resolve b7e6551 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6551
          have b7e6808 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) x) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e6629 X0 X1 X2 X3
               have i₂ := b7e524 (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3)))
               grind)
            | exact superpose b7e524 b7e6629
            | exact resolve b7e6629 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6629
          have b7e6878 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) x) x) = (k (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e6808 X0 X1 X2 X3
               have i₂ := b7e826 (M.op X0 X1) (M.op X1 (M.op X2 X3))
               grind)
            | exact superpose b7e826 b7e6808
            | exact resolve b7e6808 b7e826
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e826 b7e6808
          have b7e6936 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) x) x) := by
            intro X0 X1
            first
            | (have i₁ := b7e6878 X0 X1 x x
               have i₂ := b7e151 (M.op x x) (M.op X0 X1) X1
               grind)
            | exact superpose b7e151 b7e6878
            | exact resolve b7e6878 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6878
          have b7e6990 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (σ y)) (M.op X0 X1)) = (M.op (M.op X0 X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b7e6936 X0 X1
               have i₂ := b7e1408 X0 X1 x
               grind)
            | exact superpose b7e1408 b7e6936
            | exact resolve b7e6936 b7e1408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1408 b7e6936
          have b7e7030 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (k (M.op (M.op X0 X1) x) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e6990 X0 X1
               have i₂ := b7e524 (M.op X0 X1)
               grind)
            | exact superpose b7e524 b7e6990
            | exact resolve b7e6990 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6990
          have b7e7328 : (τ (M.op (σ y) x)) = (k (τ (M.op (σ y) x)) y) := by
            first
            | (have i₁ := b7e32 (M.op (σ y) x) y
               have i₂ := b7e1574
               grind)
            | exact superpose b7e1574 b7e32
            | exact resolve b7e32 b7e1574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e1574
          have b7e13437 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e3324 (τ X0)
               have i₂ := b7e28 X0 (τ X0)
               grind)
            | exact superpose b7e28 b7e3324
            | (have j0 := b7e3324 (τ X0)
               grind)
            | exact resolve b7e3324 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e3324
          have b7e13440 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e13437 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e13437
            | (have j0 := b7e13437 X0
               grind)
            | exact resolve b7e13437 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13437
          have b7e13444 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13440 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e13440
            | (have j0 := b7e13440 X0
               grind)
            | exact resolve b7e13440 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13440
          have b7e19300 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e1465 X0 X1
               have i₂ := b7e81 X0 X1 X2
               grind)
            | exact superpose b7e81 b7e1465
            | (have j0 := b7e1465 X2 X0
               have j1 := b7e81 X2 X0 X2
               grind)
            | (have r₁ := b7e1465 (M.op X2 X1) X1
               have r₂ := b7e81 (M.op X2 X1) X1 X2
               grind)
            | (have r₁ := b7e1465 X1 (M.op X2 X1)
               have r₂ := b7e81 (M.op X2 X1) X1 X2
               grind)
            | exact resolve b7e1465 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81 b7e1465
          have b7e19433 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e19300 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e19300
          have b7e19545 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e19433 X0 X1 X2
               have j1 := b7e122 X2 X1 X2 X0
               grind)
            | (have r₁ := b7e19433 x X2 X0
               have r₂ := b7e122 X0 x X2 x
               grind)
            | (have r₁ := b7e19433 X1 X1 (M.op X2 x)
               have r₂ := b7e122 (M.op X1 X1) X1 X2 x
               grind)
            | (have r₁ := b7e19433 X0 X1 (M.op X0 (M.op X1 X0))
               have r₂ := b7e122 X0 X1 X2 (M.op X0 (M.op X1 X0))
               grind)
            | exact resolve b7e19433 b7e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e122 b7e19433
          have b7e19653 : ∀ X0 X2 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X2
            first
            | (have i₁ := b7e19545 X0 x X2
               have i₂ := b7e151 X0 X0 x
               grind)
            | exact superpose b7e151 b7e19545
            | (have j0 := b7e19545 X0 x X2
               grind)
            | exact resolve b7e19545 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151 b7e19545
          have b7e19758 : ∀ X0 X2 : G, (M.op X0 x) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X2
            first
            | (have i₁ := b7e19653 X0 X2
               have i₂ := b7e524 X0
               grind)
            | exact superpose b7e524 b7e19653
            | (have j0 := b7e19653 X0 X2
               grind)
            | exact resolve b7e19653 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e19653
          have b7e19858 : ∀ X0 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X2
            first
            | (have j0 := b7e19758 X0 X2
               have j1 := b7e1813 X2 X0
               grind)
            | (have r₁ := b7e19758 x X2
               have r₂ := b7e1813 X0 x
               grind)
            | (have r₁ := b7e19758 x x
               have r₂ := b7e1813 X0 x
               grind)
            | exact resolve b7e19758 b7e1813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1813 b7e19758
          have b7e22815 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e45 X1 X0
               have i₂ := b7e19858 X0 (σ X1)
               grind)
            | exact superpose b7e19858 b7e45
            | (have j1 := b7e19858 X0 (σ X1)
               grind)
            | exact resolve b7e45 b7e19858
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e23595 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = X0 ∨ (k X0 (M.op X0 x)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e3126 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3126
          have b7e34202 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (k X0 (M.op X0 x)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e7030 X0 X1
               have i₂ := b7e23595 X0 X1
               grind)
            | exact superpose b7e23595 b7e7030
            | (have j1 := b7e23595 X0 X1
               grind)
            | exact resolve b7e7030 b7e23595
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7030 b7e23595
          have b7e37333 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 x)) = X0 := by
            intro X0
            first
            | (have j0 := b7e34202 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34202
          have b7e37334 : ∀ X0 : G, (k X0 (M.op X0 x)) = X0 := by
            intro X0
            first
            | (have j0 := b7e37333 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37333
          have b7e37636 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) x))) := by
            intro X0
            first
            | (have i₁ := b7e45 X0 (M.op (σ X0) x)
               have i₂ := b7e37334 (σ X0)
               grind)
            | exact superpose b7e37334 b7e45
            | exact resolve b7e45 b7e37334
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45 b7e37334
          have b7e37649 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e37636 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e37636
            | exact resolve b7e37636 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37636
          have b7e92320 : ∀ X0 : G, (τ (M.op X0 x)) = (k y (τ X0)) ∨ (M.op (σ y) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e22815 X0 y
               have i₂ := b7e524 X0
               grind)
            | exact superpose b7e524 b7e22815
            | (have j0 := b7e22815 X0 y
               grind)
            | exact resolve b7e22815 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e22815
          have b7e96037 : (k y (τ (σ y))) = (k (k y (τ (σ y))) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e7328
               have i₂ := b7e92320 (σ y)
               grind)
            | exact superpose b7e92320 b7e7328
            | (have j1 := b7e92320 (σ y)
               grind)
            | exact resolve b7e7328 b7e92320
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7328 b7e92320
          have b7e96086 : (k y y) = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e96037
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e96037
            | exact resolve b7e96037 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96037
          have b7e96130 : (k y y) = (k (k y y) y) ∨ (σ y) = (M.op (σ y) x) := by
            first
            | (have i₁ := b7e96086
               have i₂ := b7e524 (σ y)
               grind)
            | exact superpose b7e524 b7e96086
            | exact resolve b7e96086 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96086
          have b7e148462 : (M.op y y) = (k (M.op y y) y) ∨ (σ y) = (M.op (σ y) x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e96130
               have i₂ := b7e19858 y y
               grind)
            | exact superpose b7e19858 b7e96130
            | (have j1 := b7e19858 y y
               grind)
            | exact resolve b7e96130 b7e19858
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e19858 b7e96130
          have b7e148489 : (M.op y y) = (M.op (M.op y y) y) ∨ (σ y) = (M.op (σ y) x) ∨ y = (M.op y y) := by grind
          clear b7e148462
          have b7e148493 : (M.op y y) = (M.op y (σ y)) ∨ (σ y) = (M.op (σ y) x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e148489
               have i₂ := b7e222 y y
               grind)
            | exact superpose b7e222 b7e148489
            | exact resolve b7e148489 b7e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e148489
          have b7e148497 : (M.op y y) = (M.op y x) ∨ (σ y) = (M.op (σ y) x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e148493
               have i₂ := b7e524 y
               grind)
            | exact superpose b7e524 b7e148493
            | exact resolve b7e148493 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e148493
          have b7e148501 : x = (M.op y y) ∨ (σ y) = (M.op (σ y) x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e148497
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e148497
            | exact resolve b7e148497 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e148497
          have b7e148505 : (σ y) = (M.op (σ y) x) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b7e148501
               have r₂ := b7e21
               grind)
            | exact resolve b7e148501 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e148501
          have b7e148556 : y = (k y (τ (σ y))) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e37649 y
               have i₂ := b7e148505
               grind)
            | exact superpose b7e148505 b7e37649
            | exact resolve b7e37649 b7e148505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37649 b7e148505
          have b7e148777 : y = (k y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e148556
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e148556
            | exact resolve b7e148556 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e148556
          have b7e148799 : y = (M.op y y) := by
            first
            | (have j1 := b7e13444 y
               grind)
            | (have r₁ := b7e148777
               have r₂ := b7e13444 y
               grind)
            | exact resolve b7e148777 b7e13444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13444 b7e148777
          have b7e149236 : (M.op y y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b7e222 y y
               have i₂ := b7e148799
               grind)
            | exact superpose b7e148799 b7e222
            | exact resolve b7e222 b7e148799
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e222 b7e148799
          have b7e149330 : (M.op y y) = (M.op y x) := by
            first
            | (have i₁ := b7e149236
               have i₂ := b7e524 y
               grind)
            | exact superpose b7e524 b7e149236
            | exact resolve b7e149236 b7e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e524 b7e149236
          have b7e149376 : x = (M.op y y) := by
            first
            | (have i₁ := b7e149330
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e149330
            | exact resolve b7e149330 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90 b7e149330
          have b7e149390 : False := by grind
          exact b7e149390
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X3 (M.op X0 X2) X0
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X0 X1 X2
               have i₂ := b8e13 X0 X3 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e45 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
            intro X0
            grind
          clear b8e27
          have b8e76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e78 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e13 X0 X1 X2
               have i₂ := b8e18 (M.op X0 X2) X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e80 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e106 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (M.op X2 X3)) ∨ (M.op X3 X0) = (k X0 X3) ∨ (M.op X0 X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e36 X1 X2 X3 X3
               have i₂ := b8e18 X0 X3
               grind)
            | (have i₁ := b8e36 X0 X1 X2 X3
               have i₂ := b8e18 (M.op X3 X2) X1
               grind)
            | exact superpose b8e18 b8e36
            | (have j1 := b8e18 X0 X3
               grind)
            | exact resolve b8e36 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e107 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X4 X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e36 X3 X4 X0 (M.op X0 X2)
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e36
            | exact resolve b8e36 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e164 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (M.op X4 (M.op X2 X3))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e36 X0 X1 (M.op X2 X3) X4
               have i₂ := b8e33 X1 X2 X3 X0
               grind)
            | exact superpose b8e33 b8e36
            | exact resolve b8e36 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e523 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (M.op X5 X2)) := by
            intro X0 X1 X2 X5
            first
            | (have i₁ := b8e107 X2 x x X0 X5
               have i₂ := b8e164 X0 X1 x x X2
               grind)
            | exact superpose b8e164 b8e107
            | exact resolve b8e107 b8e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107
          have b8e524 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e33 X2 x x X0
               have i₂ := b8e164 X0 X1 x x X2
               grind)
            | exact superpose b8e164 b8e33
            | exact resolve b8e33 b8e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33 b8e164
          have b8e743 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 X0 X1 X2
               have i₂ := b8e523 X0 X2 X4 X3
               grind)
            | exact superpose b8e523 b8e13
            | exact resolve b8e13 b8e523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e825 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e76 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e969 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e80 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e970 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e969
               have r₂ := b8e24
               grind)
            | exact resolve b8e969 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e969
          have b8e971 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e970
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e970
            | exact resolve b8e970 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e970
          have b8e987 : ∀ X0 X1 : G, (M.op (σ (k x y)) (σ y)) = (M.op (σ y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e523 (σ y) (σ x) X1 X0
               have i₂ := b8e971
               grind)
            | exact superpose b8e971 b8e523
            | exact resolve b8e523 b8e971
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1147 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e78 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1234 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ (k x y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e743 X0 X1 X2 (σ y) (σ x)
               have i₂ := b8e971
               grind)
            | exact superpose b8e971 b8e743
            | exact resolve b8e743 b8e971
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1889 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ (M.op y x))) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1234 X0 X1 X2
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1234
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1234 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1234
          have b8e2036 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ (M.op y x))) ∨ y = (M.op x y) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e1889 X0 X1 X2
               grind)
            | (have r₁ := b8e1889 X0 X1 X2
               have r₂ := b8e21
               grind)
            | exact resolve b8e1889 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1889
          have b8e2044 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ (M.op y x))) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e2036 X0 X1 X2
               grind)
            | (have r₁ := b8e2036 X0 X1 X2
               have r₂ := b8e22
               grind)
            | exact resolve b8e2036 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2036
          have b8e31057 : ∀ X0 X1 X2 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e45 X0
               have i₂ := b8e523 (τ X0) (τ X0) X2 X1
               grind)
            | exact superpose b8e523 b8e45
            | exact resolve b8e45 b8e523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45
          have b8e40621 : ∀ X0 X1 X2 : G, (σ (k (M.op (τ (σ X0)) (τ (σ X0))) X0)) = (σ (M.op (τ (σ X0)) (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e19 (M.op (τ (σ X0)) (τ (σ X0))) X0
               have i₂ := b8e31057 (σ X0) X1 X2
               grind)
            | exact superpose b8e31057 b8e19
            | exact resolve b8e19 b8e31057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31057
          have b8e40704 : ∀ X0 X1 X2 : G, (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e40621 X0 X1 X2
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e40621
            | exact resolve b8e40621 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40621
          have b8e40777 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          clear b8e40704
          have b8e52995 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (M.op X2 X3))) = (σ (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e40777 X0 X2 X3
               have i₂ := b8e524 X0 X1 X0
               grind)
            | (have i₁ := b8e40777 X0 X2 X3
               have i₂ := b8e524 X0 X0 X1
               grind)
            | exact superpose b8e524 b8e40777
            | exact resolve b8e40777 b8e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53045 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 (M.op X1 X2))) = (σ (M.op X0 (M.op X3 X4))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e40777 X0 X3 X4
               have i₂ := b8e40777 X0 X1 X2
               grind)
            | exact superpose b8e40777 b8e40777
            | exact resolve b8e40777 b8e40777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40777
          have b8e68000 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e825 X0 X1
               have i₂ := b8e78 X0 X1 X2
               grind)
            | exact superpose b8e78 b8e825
            | (have j0 := b8e825 X2 X0
               have j1 := b8e78 X2 X0 X2
               grind)
            | (have r₁ := b8e825 (M.op X2 X1) X1
               have r₂ := b8e78 (M.op X2 X1) X1 X2
               grind)
            | (have r₁ := b8e825 X1 (M.op X2 X1)
               have r₂ := b8e78 (M.op X2 X1) X1 X2
               grind)
            | exact resolve b8e825 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e68066 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X0 (M.op X0 X2)) ∨ (k (M.op X0 X2) X0) = (M.op X0 (M.op X0 X2)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e825 (M.op X0 X2) X0
               have i₂ := b8e524 X0 X1 X2
               grind)
            | (have i₁ := b8e825 (M.op X0 X1) X0
               have i₂ := b8e524 X0 X1 X2
               grind)
            | exact superpose b8e524 b8e825
            | (have j0 := b8e825 (M.op X0 X2) X0
               grind)
            | exact resolve b8e825 b8e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e825
          have b8e68264 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e68000 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68000
          have b8e68381 : ∀ X0 X1 X2 : G, (k (M.op X0 X2) X0) = (M.op X0 (M.op X0 X2)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e68066 X0 X1 X2
               grind)
            | (have r₁ := b8e68066 x X1 X2
               have r₂ := b8e523 x X1 X2 x
               grind)
            | exact resolve b8e68066 b8e523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e523 b8e68066
          have b8e68415 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e68264 X0 X1 X2
               have j1 := b8e106 X2 X1 X2 X0
               grind)
            | (have r₁ := b8e68264 x X2 X0
               have r₂ := b8e106 X0 x X2 x
               grind)
            | (have r₁ := b8e68264 X1 X1 (M.op X2 x)
               have r₂ := b8e106 (M.op X1 X1) X1 X2 x
               grind)
            | (have r₁ := b8e68264 X0 X1 (M.op X0 (M.op X1 X0))
               have r₂ := b8e106 X0 X1 X2 (M.op X0 (M.op X1 X0))
               grind)
            | exact resolve b8e68264 b8e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106 b8e68264
          have b8e68540 : ∀ X0 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X2
            first
            | (have j0 := b8e68415 X0 x X2
               have j1 := b8e1147 X2 X0 X2
               grind)
            | (have r₁ := b8e68415 x X2 X2
               have r₂ := b8e1147 X0 x X2
               grind)
            | exact resolve b8e68415 b8e1147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1147 b8e68415
          have b8e68901 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e68540 (σ X0) (σ X1)
               grind)
            | exact superpose b8e68540 b8e19
            | (have j1 := b8e68540 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e68540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68910 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e68540 X0 (τ X1)
               grind)
            | exact superpose b8e68540 b8e26
            | (have j1 := b8e68540 X0 (τ X1)
               grind)
            | exact resolve b8e26 b8e68540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e85074 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e68910 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e68910
            | exact resolve b8e68910 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68910
          have b8e85195 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e85074 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e85074
            | (have j0 := b8e85074 X0 X1
               grind)
            | exact resolve b8e85074 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85074
          have b8e692395 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e68901 x y
               grind)
            | exact superpose b8e68901 b8e20
            | (have j1 := b8e68901 x y
               grind)
            | exact resolve b8e20 b8e68901
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68901
          have b8e692587 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b8e692395
               have i₂ := b8e971
               grind)
            | exact superpose b8e971 b8e692395
            | exact resolve b8e692395 b8e971
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e692395
          have b8e694482 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e692587
               have i₂ := b8e85195 y x
               grind)
            | exact superpose b8e85195 b8e692587
            | (have j1 := b8e85195 y x
               grind)
            | (have r₁ := b8e692587
               have r₂ := b8e85195 y x
               grind)
            | exact resolve b8e692587 b8e85195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85195 b8e692587
          have b8e694483 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by grind
          clear b8e694482
          have b8e694865 : (k x y) = (τ (σ x)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e14 (k x y)
               have i₂ := b8e694483
               grind)
            | exact superpose b8e694483 b8e14
            | exact resolve b8e14 b8e694483
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e694483
          have b8e694914 : x = (k x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e694865
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e694865
            | exact resolve b8e694865 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e694865
          have b8e695301 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e68540 y x
               have i₂ := b8e694914
               grind)
            | exact superpose b8e694914 b8e68540
            | (have j0 := b8e68540 x y
               grind)
            | exact resolve b8e68540 b8e694914
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68540 b8e694914
          have b8e695304 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e695301
          have b8e695311 : x = (M.op y x) := by
            first
            | (have r₁ := b8e695304
               have r₂ := b8e22
               grind)
            | exact resolve b8e695304 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e695304
          have b8e699427 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) := by
            intro X0
            first
            | (have i₁ := b8e524 y x X0
               have i₂ := b8e695311
               grind)
            | exact superpose b8e695311 b8e524
            | exact resolve b8e524 b8e695311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e524
          have b8e699463 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e743 X0 X1 X2 y x
               have i₂ := b8e695311
               grind)
            | exact superpose b8e695311 b8e743
            | exact resolve b8e743 b8e695311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e743
          have b8e699485 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b8e2044 X0 y x
               have i₂ := b8e695311
               grind)
            | exact superpose b8e695311 b8e2044
            | exact resolve b8e2044 b8e695311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2044
          have b8e699508 : ∀ X0 X1 : G, (σ (M.op x y)) = (σ (M.op y (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e52995 y x X0 X1
               have i₂ := b8e695311
               grind)
            | exact superpose b8e695311 b8e52995
            | exact resolve b8e52995 b8e695311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52995
          have b8e699511 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X2))) = (σ (M.op X0 x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e53045 X0 X1 X2 y x
               have i₂ := b8e695311
               grind)
            | exact superpose b8e695311 b8e53045
            | exact resolve b8e53045 b8e695311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53045
          have b8e699546 : ∀ X0 : G, (k x y) = (M.op y x) ∨ y = (M.op (M.op y X0) y) := by
            intro X0
            first
            | (have i₁ := b8e68381 y x x
               have i₂ := b8e695311
               grind)
            | exact superpose b8e695311 b8e68381
            | (have j0 := b8e68381 y X0 x
               grind)
            | exact resolve b8e68381 b8e695311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68381
          have b8e699680 : ∀ X0 : G, x = (k x y) ∨ y = (M.op (M.op y X0) y) := by
            intro X0
            first
            | (have i₁ := b8e699546 X0
               have i₂ := b8e695311
               grind)
            | exact superpose b8e695311 b8e699546
            | (have j0 := b8e699546 X0
               grind)
            | exact resolve b8e699546 b8e695311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e699546
          have b8e699685 : (σ (M.op x y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e699508 x x
               have i₂ := b8e699511 y x x
               grind)
            | exact superpose b8e699511 b8e699508
            | exact resolve b8e699508 b8e699511
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e699508 b8e699511
          have b8e699775 : y = (M.op x y) ∨ x = (k x y) := by
            first
            | (have i₁ := b8e699680 x
               have i₂ := b8e699427 x
               grind)
            | exact superpose b8e699427 b8e699680
            | exact resolve b8e699680 b8e699427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e699427 b8e699680
          have b8e699780 : (σ (M.op x y)) = (σ x) := by
            first
            | (have i₁ := b8e699685
               have i₂ := b8e695311
               grind)
            | exact superpose b8e695311 b8e699685
            | exact resolve b8e699685 b8e695311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e695311 b8e699685
          have b8e699818 : x = (k x y) := by
            first
            | (have r₁ := b8e699775
               have r₂ := b8e22
               grind)
            | exact resolve b8e699775 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e699775
          have b8e708655 : (σ (k x y)) = (M.op (σ y) x) := by
            first
            | (have i₁ := b8e971
               have i₂ := b8e699485 (σ y)
               grind)
            | exact superpose b8e699485 b8e971
            | exact resolve b8e971 b8e699485
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e971 b8e699485
          have b8e709524 : (σ x) = (M.op (σ y) x) := by
            first
            | (have i₁ := b8e708655
               have i₂ := b8e699818
               grind)
            | exact superpose b8e699818 b8e708655
            | exact resolve b8e708655 b8e699818
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e708655
          have b8e717961 : (M.op (σ (k x y)) (σ y)) = (M.op (σ y) x) := by
            first
            | (have i₁ := b8e987 x x
               have i₂ := b8e699463 (σ y) x x
               grind)
            | exact superpose b8e699463 b8e987
            | exact resolve b8e987 b8e699463
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e987 b8e699463
          have b8e718667 : (σ x) = (M.op (σ (k x y)) (σ y)) := by
            first
            | (have i₁ := b8e717961
               have i₂ := b8e709524
               grind)
            | exact superpose b8e709524 b8e717961
            | exact resolve b8e717961 b8e709524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e709524 b8e717961
          have b8e718861 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e718667
               have i₂ := b8e699818
               grind)
            | exact superpose b8e699818 b8e718667
            | exact resolve b8e718667 b8e699818
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e699818 b8e718667
          have b8e718980 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e718861
               grind)
            | exact superpose b8e718861 b8e20
            | exact resolve b8e20 b8e718861
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e718861
          have b8e719599 : False := by grind
          exact b8e719599

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_pxy_pyx_Equation4554 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4554 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
        intro X0 X1 X2 X3
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e38 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X1 (σ y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (σ y) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 : G, (M.op y y) = (M.op X0 (M.op X1 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e39 X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e39
        | exact resolve b0e39 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e44 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (σ y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e38 X0 X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e38
        | exact resolve b0e38 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e46 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e43 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e43
        | exact resolve b0e43 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e155 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e44 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e44
        | exact resolve b0e44 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e197 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e155 (σ x)
           grind)
        | exact superpose b0e155 b0e18
        | exact resolve b0e18 b0e155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e155
      have b0e202 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e197
           have i₂ := b0e46 x
           grind)
        | exact superpose b0e46 b0e197
        | exact resolve b0e197 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e197
      have b0e203 : False := by grind
      exact b0e203
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b1e27 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e25 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e97 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e17 (σ X1) (σ X0)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X0)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e5722 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e97 y y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e97
          | exact resolve b1e97 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e97
        have b1e5932 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b1e5722
        have b1e6039 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b1e5932
             have r₂ := b1e24
             grind)
          | exact resolve b1e5932 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5932
        have b1e6078 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e6039
             have i₂ := b1e27 y
             grind)
          | exact superpose b1e27 b1e6039
          | exact resolve b1e6039 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e6039
        have b1e6083 : False := by grind
        exact b1e6083
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b2e25 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
        have b2e79 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ y) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e92 : ∀ X0 : G, (M.op (σ y) (σ y)) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b2e79 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79
        have b2e187 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e26 X0 y
             have i₂ := b2e25 (τ X0)
             grind)
          | exact superpose b2e25 b2e26
          | exact resolve b2e26 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e192 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e187 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e187
          | exact resolve b2e187 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e187
        have b2e1486 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e92 X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e92 (M.op (σ y) (σ y))
             grind)
          | exact superpose b2e92 b2e21
          | (have j1 := b2e92 X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e92 (σ y)
             grind)
          | exact resolve b2e21 b2e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1525 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) ≠ X0 := by
          intro X0
          first
          | (have i₁ := b2e1486 X0
             have i₂ := b2e192 X0
             grind)
          | exact superpose b2e192 b2e1486
          | (have j0 := b2e1486 X0
             grind)
          | (have r₁ := b2e1486 (k (σ y) (σ y))
             have r₂ := b2e192 (σ y)
             grind)
          | exact resolve b2e1486 b2e192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1486
        have b2e5424 : ∀ X0 : G, (σ (k y y)) = X0 ∨ (σ y) = X0 ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e89 y y
             have i₂ := b2e92 X0
             grind)
          | (have i₁ := b2e89 X0 x
             have i₂ := b2e92 (M.op (σ X0) (σ x))
             grind)
          | exact superpose b2e92 b2e89
          | (have j1 := b2e92 X0
             grind)
          | exact resolve b2e89 b2e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89 b2e92
        have b2e5654 : ∀ X0 : G, (σ (k y y)) = X0 ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b2e5424 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5424
        have b2e5762 : ∀ X0 : G, (σ y) = X0 ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e5654 X0
             have i₂ := b2e25 y
             grind)
          | exact superpose b2e25 b2e5654
          | (have j0 := b2e5654 X0
             grind)
          | exact resolve b2e5654 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e5654
        have b2e5763 : ∀ X0 : G, (σ y) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b2e5762 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5762
        have b2e5799 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e5763 X0
             have i₂ := b2e192 X0
             grind)
          | exact superpose b2e192 b2e5763
          | (have j0 := b2e5763 X0
             grind)
          | exact resolve b2e5763 b2e192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e192 b2e5763
        have b2e5804 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e5799 X0
             have j1 := b2e1525 X0
             grind)
          | (have r₁ := b2e5799 (σ y)
             have r₂ := b2e1525 (M.op (σ y) (σ y))
             grind)
          | (have r₁ := b2e5799 X0
             have r₂ := b2e1525 X0
             grind)
          | (have r₁ := b2e5799 (σ y)
             have r₂ := b2e1525 (σ y)
             grind)
          | exact resolve b2e5799 b2e1525
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1525 b2e5799
        have b2e6599 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e5804 (σ y)
             grind)
          | exact superpose b2e5804 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e5804 (σ y)
             grind)
          | exact resolve b2e21 b2e5804
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5804
        have b2e6650 : False := by grind
        exact b2e6650
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
        have b3e27 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b3e26 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e31 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e27 (σ X0)
             have i₂ := b3e18 X0 y
             grind)
          | exact superpose b3e18 b3e27
          | exact resolve b3e27 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e34 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e31 X0
             grind)
          | exact superpose b3e31 b3e13
          | exact resolve b3e13 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e35 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e34 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e34
          | exact resolve b3e34 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e106 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) ∨ (M.op y y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e35 X0
             have i₂ := b3e17 X0 y
             grind)
          | exact superpose b3e17 b3e35
          | (have j1 := b3e17 y y
             grind)
          | exact resolve b3e35 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e112 : ∀ X0 : G, x = y ∨ (M.op y X0) = X0 ∨ (M.op y y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e106 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e106
          | (have j0 := b3e106 X0
             grind)
          | exact resolve b3e106 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106
        have b3e119 : ∀ X0 : G, (M.op y X0) = X0 ∨ (M.op y y) = X0 := by
          intro X0
          first
          | (have j0 := b3e112 X0
             grind)
          | (have r₁ := b3e112 X0
             have r₂ := b3e24
             grind)
          | exact resolve b3e112 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e112
        have b3e122 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e119 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e119
          | (have j0 := b3e119 X0
             grind)
          | exact resolve b3e119 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e119
        have b3e3113 : x = y ∨ x = y := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e122 y
             grind)
          | exact superpose b3e122 b3e21
          | (have j1 := b3e122 y
             grind)
          | exact resolve b3e21 b3e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e122
        have b3e3149 : x = y := by grind
        clear b3e3113
        have b3e3172 : False := by grind
        exact b3e3172
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y y) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : x ≠ y := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e21
            | exact resolve b4e21 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e59 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          have b4e60 : (M.op x y) = (k x y) ∨ x = y := by grind
          have b4e61 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e60
               have r₂ := b4e27
               grind)
            | exact resolve b4e60 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e60
          have b4e62 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e59
               have r₂ := b4e26
               grind)
            | exact resolve b4e59 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e59
          have b4e63 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e62
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e62
            | exact resolve b4e62 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e64 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e63
               have i₂ := b4e61
               grind)
            | exact superpose b4e61 b4e63
            | exact resolve b4e63 b4e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61 b4e63
          have b4e65 : False := by grind
          exact b4e65
        · have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y y) := by grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X0)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3967 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e76 y y
               grind)
            | exact superpose b5e76 b5e24
            | (have j1 := b5e76 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e76 y x
               grind)
            | exact resolve b5e24 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e4094 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e3967
          have b5e4141 : (σ x) ≠ (σ (k y y)) := by
            first
            | (have r₁ := b5e4094
               have r₂ := b5e23
               grind)
            | exact resolve b5e4094 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4094
          have b5e4177 : (σ x) ≠ (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e4141
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e4141
            | (have j1 := b5e18 y y
               grind)
            | exact resolve b5e4141 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4141
          have b5e4182 : (σ x) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b5e4177
          have b5e4187 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e4182
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e4182
            | exact resolve b5e4182 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4182
          have b5e4188 : y = (M.op y y) := by grind
          clear b5e4187
          have b5e4797 : x = y := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e4188
               grind)
            | exact superpose b5e4188 b5e22
            | exact resolve b5e22 b5e4188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4188
          have b5e4827 : False := by grind
          exact b5e4827
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
        have b6e25 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e29 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e25 (σ X0)
             have i₂ := b6e18 X0 y
             grind)
          | exact superpose b6e18 b6e25
          | exact resolve b6e25 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e32 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e29 X0
             grind)
          | exact superpose b6e29 b6e13
          | exact resolve b6e13 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e33 : ∀ X0 : G, (k X0 y) = X0 := by
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
        have b6e106 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) ∨ (M.op y y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e33 X0
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e33
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e33 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e112 : ∀ X0 : G, (M.op y X0) = X0 ∨ (M.op y y) = X0 := by
          intro X0
          first
          | (have j0 := b6e106 X0
             grind)
          | (have r₁ := b6e106 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e106 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e106 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106
        have b6e6131 : y ≠ y ∨ y = (M.op y y) := by
          first
          | (have j0 := b6e112 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e112
        have b6e6132 : y = (M.op y y) := by grind
        clear b6e6131
        have b6e6135 : False := by grind
        exact b6e6135
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y y) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 X0
               have i₂ := b7e18 (σ X1) (σ X0)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X0) (σ X0)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e80 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e18 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e70 X0 X1
               have j1 := b7e80 X1 X0
               grind)
            | (have r₁ := b7e70 X0 X1
               have r₂ := b7e80 (k X0 X1) (M.op X0 X1)
               grind)
            | (have r₁ := b7e70 X0 X1
               have r₂ := b7e80 (M.op X0 X1) (k X0 X1)
               grind)
            | (have r₁ := b7e70 X0 X1
               have r₂ := b7e80 X0 X1
               grind)
            | exact resolve b7e70 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e80
          have b7e3228 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e77 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e77
            | exact resolve b7e77 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e3434 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e3228
          have b7e3496 : (σ x) = (σ (k y y)) := by
            first
            | (have r₁ := b7e3434
               have r₂ := b7e26
               grind)
            | exact resolve b7e3434 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e3434
          have b7e3558 : (k y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e3496
               grind)
            | exact superpose b7e3496 b7e14
            | exact resolve b7e14 b7e3496
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3496
          have b7e3573 : x = (k y y) := by
            first
            | (have i₁ := b7e3558
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e3558
            | exact resolve b7e3558 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3558
          have b7e4046 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e84 y y
               have i₂ := b7e3573
               grind)
            | exact superpose b7e3573 b7e84
            | (have j0 := b7e84 x y
               grind)
            | exact resolve b7e84 b7e3573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84 b7e3573
          have b7e4049 : x = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b7e4046
          have b7e4055 : y = (M.op y y) := by
            first
            | (have r₁ := b7e4049
               have r₂ := b7e22
               grind)
            | exact resolve b7e4049 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4049
          have b7e4065 : False := by grind
          exact b7e4065
        · have b8e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
            intro X0 X1 X2 X3
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b8e30 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X4) X0) := by
            intro X0 X1 X4
            first
            | (have i₁ := b8e13 x x X0 X4
               have i₂ := b8e13 x x X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) X0) X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 X2 X3 X4 (M.op x X0)
               have i₂ := b8e13 X4 x X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 X0 X1 X2 x
               have i₂ := b8e13 X3 X4 X2 x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op X3 (M.op X4 X0))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 X2 X3 (M.op X4 X0) x
               have i₂ := b8e13 (M.op (M.op X4 X0) x) X4 X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e40 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e61 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e64 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X0 X3) ∨ (M.op X3 X3) = X3 ∨ (M.op X3 X0) = (k X0 X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 X2 X3 X3
               have i₂ := b8e18 X0 X3
               grind)
            | (have i₁ := b8e13 X0 X1 X2 X3
               have i₂ := b8e18 (M.op X2 X3) X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X3 X3
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ y) (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X0) (σ X0)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e74 : ∀ X0 : G, (M.op (σ y) (σ y)) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b8e61 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e76 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b8e67 X0
               grind)
            | (have r₁ := b8e67 X0
               have r₂ := b8e23
               grind)
            | exact resolve b8e67 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e78 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e62 X0 X1
               have j1 := b8e73 X1 X0
               grind)
            | (have r₁ := b8e62 X0 X1
               have r₂ := b8e73 (k X0 X1) (M.op X0 X1)
               grind)
            | (have r₁ := b8e62 X0 X1
               have r₂ := b8e73 (M.op X0 X1) (k X0 X1)
               grind)
            | (have r₁ := b8e62 X0 X1
               have r₂ := b8e73 X0 X1
               grind)
            | exact resolve b8e62 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62 b8e73
          have b8e101 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X0) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e30 X2 X3 (M.op x X0)
               have i₂ := b8e13 X2 x X0 X1
               grind)
            | exact superpose b8e13 b8e30
            | exact resolve b8e30 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e151 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op X1 (M.op X2 X3)) ∨ (M.op X3 X3) = X3 ∨ (M.op X3 X0) = (k X0 X3) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e34 X1 X2 X3 X4 X3
               have i₂ := b8e18 X0 X3
               grind)
            | (have i₁ := b8e34 X0 X1 X2 X3 X4
               have i₂ := b8e18 (M.op X4 X2) X1
               grind)
            | exact superpose b8e18 b8e34
            | (have j1 := b8e18 X3 X3
               grind)
            | exact resolve b8e34 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e182 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X5) X3) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b8e30 X3 (M.op x X2) X5
               have i₂ := b8e34 X3 x X2 X0 X1
               grind)
            | (have i₁ := b8e30 X3 (M.op x X2) X5
               have i₂ := b8e34 X0 X1 X2 X3 x
               grind)
            | exact superpose b8e34 b8e30
            | exact resolve b8e30 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e183 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X5)) = (M.op (M.op X0 (M.op X1 X2)) X5) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e13 X3 X4 X5 (M.op x X2)
               have i₂ := b8e34 X5 x X2 X0 X1
               grind)
            | (have i₁ := b8e13 X3 X4 X5 (M.op x X2)
               have i₂ := b8e34 X0 X1 X2 X5 x
               grind)
            | exact superpose b8e34 b8e13
            | exact resolve b8e13 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e220 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 (M.op X4 X5)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X6) X5) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b8e32 X6 (M.op x X2) X3 X4 X5
               have i₂ := b8e32 X0 X1 X6 x X2
               grind)
            | exact superpose b8e32 b8e32
            | exact resolve b8e32 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e399 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 (M.op (M.op X0 X1) X0)) = (M.op X2 (M.op X3 (M.op X4 (M.op X5 X0)))) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b8e34 X2 X3 (M.op X4 (M.op X5 X0)) X6 x
               have i₂ := b8e35 X0 X1 x X4 X5
               grind)
            | exact superpose b8e35 b8e34
            | exact resolve b8e34 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e406 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op X3 (M.op X4 (M.op X5 X0)))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e32 x x X2 X3 (M.op X4 (M.op X5 X0))
               have i₂ := b8e35 X0 X1 (M.op (M.op x x) x) X4 X5
               grind)
            | exact superpose b8e35 b8e32
            | exact resolve b8e32 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e439 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e76 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e440 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e439
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e439
            | exact resolve b8e439 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e439
          have b8e639 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e74 X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e74 (M.op (σ y) (σ y))
               grind)
            | exact superpose b8e74 b8e23
            | (have j1 := b8e74 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e74 (σ y)
               grind)
            | exact resolve b8e23 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e1153 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e3023 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e70 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
          have b8e3026 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e3023 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3023
          have b8e5179 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) X3) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e101 X5 (M.op x X2) X3 X4
               have i₂ := b8e34 X5 x X2 X0 X1
               grind)
            | (have i₁ := b8e101 X5 (M.op x X2) X3 X4
               have i₂ := b8e34 X0 X1 X2 X5 x
               grind)
            | exact superpose b8e34 b8e101
            | exact resolve b8e101 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e101
          have b8e5570 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 (σ (k x y))) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e182 X2 (σ y) (σ x) X0 X1
               have i₂ := b8e440
               grind)
            | exact superpose b8e440 b8e182
            | exact resolve b8e182 b8e440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e182
          have b8e6269 : ∀ X0 X1 X2 X3 X4 X6 X7 X8 : G, (M.op X6 (M.op X7 (M.op X8 X4))) = (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X4) := by
            intro X0 X1 X2 X3 X4 X6 X7 X8
            first
            | (have i₁ := b8e35 X4 (M.op x X3) X6 X7 X8
               have i₂ := b8e183 X0 X1 X2 X4 x X3
               grind)
            | exact superpose b8e183 b8e35
            | exact resolve b8e35 b8e183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35 b8e183
          have b8e7160 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have j0 := b8e639 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e639
          have b8e7161 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b8e7160
               have i₂ := b8e19 y y
               grind)
            | exact superpose b8e19 b8e7160
            | exact resolve b8e7160 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7160
          have b8e7174 : (σ y) ≠ (σ (k y y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e7161
               grind)
            | exact superpose b8e7161 b8e23
            | exact resolve b8e23 b8e7161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7161
          have b8e15246 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e3026 (τ X0)
               have i₂ := b8e27 X0 (τ X0)
               grind)
            | exact superpose b8e27 b8e3026
            | (have j0 := b8e3026 (τ X0)
               grind)
            | exact resolve b8e3026 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3026
          have b8e15286 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e15246 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e15246
            | (have j0 := b8e15246 X0
               grind)
            | exact resolve b8e15246 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15246
          have b8e15305 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e15286 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e15286
            | (have j0 := b8e15286 X0
               grind)
            | exact resolve b8e15286 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15286
          have b8e16360 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op (σ (k x y)) (σ y)) X3) X4) X2) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e220 (σ y) (σ x) X3 X0 X1 X2 X4
               have i₂ := b8e440
               grind)
            | exact superpose b8e440 b8e220
            | exact resolve b8e220 b8e440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e220 b8e440
          have b8e25682 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X2 X3) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X3) = (k X3 X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X3) = (k X3 X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e1153 X3 X2
               have i₂ := b8e64 X3 X0 X1 X2
               grind)
            | exact superpose b8e64 b8e1153
            | (have j0 := b8e1153 X3 X2
               have j1 := b8e64 X3 X1 X2 X2
               grind)
            | (have r₁ := b8e1153 X3 (M.op X2 X3)
               have r₂ := b8e64 (M.op X2 X3) X3 X2 X3
               grind)
            | (have r₁ := b8e1153 (M.op X2 X1) X1
               have r₂ := b8e64 (M.op X2 X1) X1 X2 X1
               grind)
            | exact resolve b8e1153 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64 b8e1153
          have b8e25816 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X2 X3) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X3) = (k X3 X2) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b8e25682 X0 X1 X2 X3
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25682
          have b8e25870 : ∀ X2 X3 : G, (M.op X2 X2) = X2 ∨ (M.op X2 X3) = (k X3 X2) := by
            intro X2 X3
            first
            | (have j0 := b8e25816 x x X2 X3
               have j1 := b8e151 X3 x X2 X2 x
               grind)
            | (have r₁ := b8e25816 x x x (M.op X2 X3)
               have r₂ := b8e151 (M.op x x) x X2 X3 x
               grind)
            | (have r₁ := b8e25816 x X2 x x
               have r₂ := b8e151 x x X2 x x
               grind)
            | (have r₁ := b8e25816 (M.op x x) x x x
               have r₂ := b8e151 x x X2 (M.op x x) x
               grind)
            | exact resolve b8e25816 b8e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e151 b8e25816
          have b8e26028 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e25870 X0 X2
               grind)
            | exact superpose b8e25870 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e25870 X0 X2
               grind)
            | (have r₁ := b8e16 X0 X2
               have r₂ := b8e25870 X2 x
               grind)
            | exact resolve b8e16 b8e25870
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e26235 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e25870 (σ y) X0
               grind)
            | exact superpose b8e25870 b8e23
            | (have j1 := b8e25870 (σ y) X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e25870 (σ y) x
               grind)
            | exact resolve b8e23 b8e25870
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25870
          have b8e26349 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b8e26235 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26235
          have b8e26350 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e26028 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26028
          have b8e26623 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b8e40 X0 y
               have i₂ := b8e26349 X0
               grind)
            | exact superpose b8e26349 b8e40
            | exact resolve b8e40 b8e26349
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40
          have b8e26632 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 y
               have i₂ := b8e26349 (σ X0)
               grind)
            | exact superpose b8e26349 b8e19
            | exact resolve b8e19 b8e26349
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e27337 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X0)) = (k (τ (M.op X2 X0)) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e26623 (M.op X2 X0)
               have i₂ := b8e13 (σ y) X2 X0 X1
               grind)
            | exact superpose b8e13 b8e26623
            | exact resolve b8e26623 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e27340 : ∀ X0 X1 X2 X3 : G, (τ (M.op X0 (M.op X1 X2))) = (k (τ (M.op X3 X2)) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e26623 (M.op X3 X2)
               have i₂ := b8e34 (σ y) X3 X2 X0 X1
               grind)
            | (have i₁ := b8e26623 (M.op X3 X2)
               have i₂ := b8e34 X0 X1 X2 (σ y) X3
               grind)
            | exact superpose b8e34 b8e26623
            | exact resolve b8e26623 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26623
          have b8e29717 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op X3 (σ (k X0 y))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e34 X1 X2 (σ X0) X3 (σ y)
               have i₂ := b8e26632 X0
               grind)
            | exact superpose b8e26632 b8e34
            | exact resolve b8e34 b8e26632
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26632
          have b8e106730 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 X2) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e48 X0 X1
               have i₂ := b8e26350 X1 (σ X0) X2
               grind)
            | exact superpose b8e26350 b8e48
            | (have j1 := b8e26350 X1 X1 X2
               grind)
            | exact resolve b8e48 b8e26350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e106777 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b8e7174
               have i₂ := b8e26350 y y X0
               grind)
            | exact superpose b8e26350 b8e7174
            | (have j1 := b8e26350 y x X0
               grind)
            | exact resolve b8e7174 b8e26350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7174
          have b8e106969 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e26350 X0 X2 (τ X1)
               grind)
            | exact superpose b8e26350 b8e26
            | (have j1 := b8e26350 X0 X2 X2
               grind)
            | exact resolve b8e26 b8e26350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e107033 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e26350 X1 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26350
          have b8e107034 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b8e106777 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106777
          have b8e107042 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 X2) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e106730 X0 X1 X2
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e106730
            | (have j0 := b8e106730 X0 X1 X2
               grind)
            | exact resolve b8e106730 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106730
          have b8e107154 : ∀ X0 : G, (τ (M.op y (σ X0))) = (k X0 (τ y)) := by
            intro X0
            first
            | (have i₁ := b8e48 X0 y
               have i₂ := b8e107034 (σ X0)
               grind)
            | exact superpose b8e107034 b8e48
            | exact resolve b8e48 b8e107034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48
          have b8e107156 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 y
               have i₂ := b8e107034 (τ X0)
               grind)
            | exact superpose b8e107034 b8e26
            | exact resolve b8e26 b8e107034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e107216 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e107156 X0
               have i₂ := b8e26349 X0
               grind)
            | exact superpose b8e26349 b8e107156
            | exact resolve b8e107156 b8e26349
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26349 b8e107156
          have b8e108003 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X3 X4)))) ≠ (M.op (M.op X4 X6) X4) ∨ (M.op (M.op X4 X6) X4) = (k (M.op (M.op X4 X6) X4) X5) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b8e107033 (M.op (M.op X4 X6) X4) X5
               have i₂ := b8e399 X4 X6 X0 X1 X2 X3 X5
               grind)
            | exact superpose b8e399 b8e107033
            | (have j0 := b8e107033 (M.op (M.op X4 X6) X4) X5
               grind)
            | exact resolve b8e107033 b8e399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e399 b8e107033
          have b8e108112 : ∀ X4 X5 X6 : G, (M.op (M.op X4 X6) X4) = (k (M.op (M.op X4 X6) X4) X5) := by
            intro X4 X5 X6
            first
            | (have j0 := b8e108003 x x x x X4 X5 X6
               grind)
            | (have r₁ := b8e108003 x x X4 X5 x X5 x
               have r₂ := b8e406 x x x x X4 X5
               grind)
            | exact resolve b8e108003 b8e406
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e406 b8e108003
          have b8e109035 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b8e107216 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e107216
            | exact resolve b8e107216 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e109061 : ∀ X0 : G, (τ (M.op (σ y) X0)) = (M.op y (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op y (τ X0))
               have i₂ := b8e107216 X0
               grind)
            | exact superpose b8e107216 b8e14
            | exact resolve b8e14 b8e107216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107216
          have b8e440544 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (τ (σ X0))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e107042 X2 (σ X0) (σ X1)
               grind)
            | exact superpose b8e107042 b8e19
            | (have j1 := b8e107042 X2 (σ X0) X2
               grind)
            | exact resolve b8e19 b8e107042
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107042
          have b8e440600 : ∀ X0 X1 X2 : G, (k X2 X0) = X2 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e440544 X0 X1 X2
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e440544
            | (have j0 := b8e440544 X0 X1 X2
               grind)
            | exact resolve b8e440544 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e440544
          have b8e477162 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X1) X0)) = (k (M.op y (τ X0)) y) := by
            intro X0 X1
            first
            | (have i₁ := b8e27337 X0 X1 (σ y)
               have i₂ := b8e109061 X0
               grind)
            | exact superpose b8e109061 b8e27337
            | exact resolve b8e27337 b8e109061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109061
          have b8e477287 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X1) X0)) = (M.op y (M.op y (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e477162 X0 X1
               have i₂ := b8e107034 (M.op y (τ X0))
               grind)
            | exact superpose b8e107034 b8e477162
            | exact resolve b8e477162 b8e107034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e477162
          have b8e483113 : ∀ X0 X1 X2 X3 : G, (τ (M.op X0 (M.op X1 X2))) = (τ (M.op (M.op X2 X3) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e27337 X2 X3 x
               have i₂ := b8e27340 X0 X1 X2 x
               grind)
            | exact superpose b8e27340 b8e27337
            | exact resolve b8e27337 b8e27340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27337 b8e27340
          have b8e483171 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 X2))) = (M.op y (M.op y (τ X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e483113 X0 X1 X2 x
               have i₂ := b8e477287 X2 x
               grind)
            | exact superpose b8e477287 b8e483113
            | exact resolve b8e483113 b8e477287
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e477287 b8e483113
          have b8e490101 : ∀ X0 X1 X4 : G, (M.op X0 (σ (k X1 y))) = (M.op X4 (σ (k X1 y))) := by
            intro X0 X1 X4
            first
            | (have i₁ := b8e29717 X1 x x X4
               have i₂ := b8e29717 X1 x x X0
               grind)
            | exact superpose b8e29717 b8e29717
            | exact resolve b8e29717 b8e29717
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e490812 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ X2))) = (σ (M.op y (k X2 y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e109035 (k X2 y)
               have i₂ := b8e29717 X2 X0 X1 (σ y)
               grind)
            | exact superpose b8e29717 b8e109035
            | exact resolve b8e109035 b8e29717
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e490830 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 (σ X2)))) = (k (k X2 y) (τ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e107154 (k X2 y)
               have i₂ := b8e29717 X2 X0 X1 y
               grind)
            | exact superpose b8e29717 b8e107154
            | exact resolve b8e107154 b8e29717
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29717
          have b8e490856 : ∀ X0 X1 X2 : G, (k (M.op y X2) (τ y)) = (τ (M.op X0 (M.op X1 (σ X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e490830 X0 X1 X2
               have i₂ := b8e107034 X2
               grind)
            | exact superpose b8e107034 b8e490830
            | exact resolve b8e490830 b8e107034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e490830
          have b8e490861 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ X2))) = (σ (M.op y (M.op y X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e490812 X0 X1 X2
               have i₂ := b8e107034 X2
               grind)
            | exact superpose b8e107034 b8e490812
            | exact resolve b8e490812 b8e107034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e490812
          have b8e491031 : ∀ X0 X1 X4 : G, (M.op X0 (σ (M.op y X1))) = (M.op X4 (σ (M.op y X1))) := by
            intro X0 X1 X4
            first
            | (have i₁ := b8e490101 X0 X0 X4
               have i₂ := b8e107034 X0
               grind)
            | exact superpose b8e107034 b8e490101
            | exact resolve b8e490101 b8e107034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e490101
          have b8e491059 : ∀ X2 : G, (k (M.op y X2) (τ y)) = (M.op y (M.op y (τ (σ X2)))) := by
            intro X2
            first
            | (have i₁ := b8e490856 x x X2
               have i₂ := b8e483171 x x (σ X2)
               grind)
            | exact superpose b8e483171 b8e490856
            | exact resolve b8e490856 b8e483171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e483171 b8e490856
          have b8e491121 : ∀ X2 : G, (k (M.op y X2) (τ y)) = (M.op y (M.op y X2)) := by
            intro X2
            first
            | (have i₁ := b8e491059 X2
               have i₂ := b8e14 X2
               grind)
            | exact superpose b8e14 b8e491059
            | exact resolve b8e491059 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e491059
          have b8e495009 : ∀ X0 : G, (σ (M.op y (M.op y X0))) = (k (σ (M.op y X0)) y) := by
            intro X0
            first
            | (have i₁ := b8e27 y (M.op y X0)
               have i₂ := b8e491121 X0
               grind)
            | exact superpose b8e491121 b8e27
            | exact resolve b8e27 b8e491121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27 b8e491121
          have b8e495017 : ∀ X0 : G, (σ (M.op y (M.op y X0))) = (M.op y (σ (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b8e495009 X0
               have i₂ := b8e107034 (σ (M.op y X0))
               grind)
            | exact superpose b8e107034 b8e495009
            | exact resolve b8e495009 b8e107034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e495009
          have b8e604892 : ∀ X0 X1 : G, (M.op X0 (σ (M.op y X1))) = (σ (M.op y (M.op y X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e109035 (M.op y X1)
               have i₂ := b8e491031 (σ y) X1 X0
               grind)
            | (have i₁ := b8e109035 (M.op y X1)
               have i₂ := b8e491031 X0 X1 (σ y)
               grind)
            | exact superpose b8e491031 b8e109035
            | exact resolve b8e109035 b8e491031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109035 b8e491031
          have b8e716081 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X4 (σ X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e490861 X3 X4 X2
               have i₂ := b8e34 y y X2 X0 X1
               grind)
            | (have i₁ := b8e490861 X3 X4 X2
               have i₂ := b8e34 X0 X1 X2 y y
               grind)
            | exact superpose b8e34 b8e490861
            | exact resolve b8e490861 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e490861
          have b8e726551 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X2))) = (M.op y (σ (M.op y X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e495017 X2
               have i₂ := b8e34 y y X2 X0 X1
               grind)
            | (have i₁ := b8e495017 X2
               have i₂ := b8e34 X0 X1 X2 y y
               grind)
            | exact superpose b8e34 b8e495017
            | exact resolve b8e495017 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e495017
          have b8e740852 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (M.op X1 X2))) = (M.op X3 (σ (M.op y X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e604892 X3 X2
               have i₂ := b8e34 y y X2 X0 X1
               grind)
            | (have i₁ := b8e604892 X3 X2
               have i₂ := b8e34 X0 X1 X2 y y
               grind)
            | exact superpose b8e34 b8e604892
            | exact resolve b8e604892 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34 b8e604892
          have b8e835511 : ∀ X0 X1 X4 X5 : G, (σ (M.op (M.op X0 X1) X0)) = (M.op X4 (M.op X5 (σ X0))) := by
            intro X0 X1 X4 X5
            first
            | (have i₁ := b8e716081 x x X0 X4 X5
               have i₂ := b8e13 x x X0 X1
               grind)
            | exact superpose b8e13 b8e716081
            | exact resolve b8e716081 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e716081
          have b8e844752 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (τ (M.op y (σ (M.op y X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e14 (M.op X1 (M.op X2 X0))
               have i₂ := b8e726551 X1 X2 X0
               grind)
            | exact superpose b8e726551 b8e14
            | exact resolve b8e14 b8e726551
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e726551
          have b8e844776 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (k (M.op y X0) (τ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e844752 X0 X1 X2
               have i₂ := b8e107154 (M.op y X0)
               grind)
            | exact superpose b8e107154 b8e844752
            | exact resolve b8e844752 b8e107154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107154 b8e844752
          have b8e868856 : ∀ X0 X1 X4 : G, (σ (M.op (M.op X0 X1) X0)) = (M.op X4 (σ (M.op y X0))) := by
            intro X0 X1 X4
            first
            | (have i₁ := b8e740852 x x X0 X4
               have i₂ := b8e13 x x X0 X1
               grind)
            | exact superpose b8e13 b8e740852
            | exact resolve b8e740852 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e740852
          have b8e2718080 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e106969 X1 (σ X0) X2
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e106969
            | (have j0 := b8e106969 X1 X1 X2
               grind)
            | exact resolve b8e106969 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106969
          have b8e2718101 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e2718080 X0 X1 X2
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e2718080
            | (have j0 := b8e2718080 X0 X1 X2
               grind)
            | exact resolve b8e2718080 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2718080
          have b8e2740530 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b8e20
               have i₂ := b8e440600 x y X0
               grind)
            | exact superpose b8e440600 b8e20
            | (have j1 := b8e440600 x x X0
               grind)
            | exact resolve b8e20 b8e440600
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e440600
          have b8e2740575 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b8e2740530 X0
               have j1 := b8e2718101 X0 x X0
               grind)
            | (have r₁ := b8e2740530 X0
               have r₂ := b8e2718101 y x x
               grind)
            | exact resolve b8e2740530 b8e2718101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2718101 b8e2740530
          have b8e2741375 : x ≠ x ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e15305 x
               have i₂ := b8e2740575 x
               grind)
            | exact superpose b8e2740575 b8e15305
            | (have j0 := b8e15305 x
               grind)
            | (have r₁ := b8e15305 x
               have r₂ := b8e2740575 x
               grind)
            | exact resolve b8e15305 b8e2740575
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15305 b8e2740575
          have b8e2741428 : x = (M.op x x) := by grind
          clear b8e2741375
          have b8e2741925 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e30 x X0 x
               have i₂ := b8e2741428
               grind)
            | exact superpose b8e2741428 b8e30
            | exact resolve b8e30 b8e2741428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e2742155 : ∀ X0 : G, (M.op X0 (σ (M.op y x))) = (σ (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b8e868856 x x X0
               have i₂ := b8e2741428
               grind)
            | exact superpose b8e2741428 b8e868856
            | exact resolve b8e868856 b8e2741428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e868856
          have b8e2742166 : ∀ X0 : G, (σ x) = (M.op X0 (σ (M.op y x))) := by
            intro X0
            first
            | (have i₁ := b8e2742155 X0
               have i₂ := b8e2741428
               grind)
            | exact superpose b8e2741428 b8e2742155
            | exact resolve b8e2742155 b8e2741428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2742155
          have b8e2742253 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
            intro X0
            first
            | (have i₁ := b8e2741925 X0
               have i₂ := b8e2741428
               grind)
            | exact superpose b8e2741428 b8e2741925
            | exact resolve b8e2741925 b8e2741428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2741428 b8e2741925
          have b8e2745599 : ∀ X1 : G, x = (k x X1) := by
            intro X1
            first
            | (have i₁ := b8e108112 x x x
               have i₂ := b8e2742253 x
               grind)
            | exact superpose b8e2742253 b8e108112
            | exact resolve b8e108112 b8e2742253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108112
          have b8e2745677 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e5179 x x x X0 X1 x
               have i₂ := b8e2742253 (M.op x x)
               grind)
            | exact superpose b8e2742253 b8e5179
            | exact resolve b8e5179 b8e2742253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5179
          have b8e2745682 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X3))) = (M.op x X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e6269 x x x x X3 X0 X1 X2
               have i₂ := b8e2742253 (M.op x x)
               grind)
            | exact superpose b8e2742253 b8e6269
            | exact resolve b8e6269 b8e2742253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6269 b8e2742253
          have b8e2747497 : x = (M.op y x) := by
            first
            | (have i₁ := b8e107034 x
               have i₂ := b8e2745599 y
               grind)
            | exact superpose b8e2745599 b8e107034
            | exact resolve b8e107034 b8e2745599
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2748295 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op (M.op X2 X3) X2)) = (M.op X4 (M.op X0 (M.op X1 (σ X2)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e835511 X2 X3 X4 (M.op (M.op (M.op (σ (k x y)) (σ y)) x) x)
               have i₂ := b8e16360 X0 X1 (σ X2) x x
               grind)
            | exact superpose b8e16360 b8e835511
            | exact resolve b8e835511 b8e16360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16360 b8e835511
          have b8e2748516 : ∀ X2 X3 : G, (σ (M.op (M.op X2 X3) X2)) = (M.op x (σ X2)) := by
            intro X2 X3
            first
            | (have i₁ := b8e2748295 x x X2 X3 x
               have i₂ := b8e2745682 x x x (σ X2)
               grind)
            | exact superpose b8e2745682 b8e2748295
            | exact resolve b8e2748295 b8e2745682
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2745682 b8e2748295
          have b8e2748628 : ∀ X2 : G, (σ (M.op x X2)) = (M.op x (σ X2)) := by
            intro X2
            first
            | (have i₁ := b8e2748516 X2 x
               have i₂ := b8e2745677 X2 x
               grind)
            | exact superpose b8e2745677 b8e2748516
            | exact resolve b8e2748516 b8e2745677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2745677 b8e2748516
          have b8e2749110 : ∀ X0 : G, (M.op X0 x) = (k x (τ y)) := by
            intro X0
            first
            | (have i₁ := b8e844776 x x y
               have i₂ := b8e2747497
               grind)
            | exact superpose b8e2747497 b8e844776
            | exact resolve b8e844776 b8e2747497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e844776 b8e2747497
          have b8e2749118 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b8e2749110 X0
               have i₂ := b8e2745599 (τ y)
               grind)
            | exact superpose b8e2745599 b8e2749110
            | exact resolve b8e2749110 b8e2745599
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2745599 b8e2749110
          have b8e2750273 : ∀ X0 X1 : G, (M.op (M.op X1 (σ (k x y))) X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e5570 X0 x X1
               have i₂ := b8e2749118 X0
               grind)
            | exact superpose b8e2749118 b8e5570
            | exact resolve b8e5570 b8e2749118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5570 b8e2749118
          have b8e2751306 : ∀ X0 X1 : G, (M.op (M.op X1 (σ (M.op y x))) X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e2750273 X0 X1
               have i₂ := b8e107034 x
               grind)
            | exact superpose b8e107034 b8e2750273
            | exact resolve b8e2750273 b8e107034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107034 b8e2750273
          have b8e2751449 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b8e2751306 X0 x
               have i₂ := b8e2742166 x
               grind)
            | exact superpose b8e2742166 b8e2751306
            | exact resolve b8e2751306 b8e2742166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2742166 b8e2751306
          have b8e2761852 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2751449 (σ y)
               grind)
            | exact superpose b8e2751449 b8e20
            | exact resolve b8e20 b8e2751449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2751449
          have b8e2762469 : False := by grind
          exact b8e2762469
