import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3495`: `x ◇ x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_x_pxy_pyx_Equation3495 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3495 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e34 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X2 X3 X4
           have i₂ := b0e11 X2 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X0 X0) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 (M.op (M.op X2 X3) X0) X3
           have i₂ := b0e11 X0 X3 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op x (M.op y X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op y X0) (M.op (M.op X0 X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 (M.op y X0) x
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e701 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X0 X0)) = (M.op X4 (M.op (M.op X5 X4) (M.op (M.op X1 X1) X0))) := by
        intro X0 X1 X4 X5
        first
        | (have i₁ := b0e34 X1 (M.op x x) (M.op (M.op X1 X1) X0) X4 X5
           have i₂ := b0e38 X1 X0 x x
           grind)
        | exact superpose b0e38 b0e34
        | exact resolve b0e34 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e709 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y (M.op (M.op X0 X0) X0))) := by
        intro X0
        first
        | (have i₁ := b0e35 (M.op (M.op X0 X0) X0)
           have i₂ := b0e38 X0 X0 X0 X0
           grind)
        | exact superpose b0e38 b0e35
        | exact resolve b0e35 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e725 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op x (M.op y (M.op (M.op X1 X1) X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e701 X0 X1 x x
           have i₂ := b0e43 (M.op (M.op X1 X1) X0) x x
           grind)
        | exact superpose b0e43 b0e701
        | exact resolve b0e701 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e701
      have b0e1494 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y x) (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e47 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e47
        | exact resolve b0e47 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e1808 : (M.op x x) = (M.op x (M.op y (M.op y x))) := by
        first
        | (have i₁ := b0e1494 x
           have i₂ := b0e35 (M.op y x)
           grind)
        | exact superpose b0e35 b0e1494
        | exact resolve b0e1494 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e1859 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op y (M.op y X0))) := by
        intro X0
        first
        | (have i₁ := b0e43 (M.op y X0) x y
           have i₂ := b0e1494 X0
           grind)
        | exact superpose b0e1494 b0e43
        | exact resolve b0e43 b0e1494
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e1494
      have b0e1923 : (M.op x x) = (M.op x (M.op x x)) := by
        first
        | (have i₁ := b0e1808
           have i₂ := b0e1859 x
           grind)
        | exact superpose b0e1859 b0e1808
        | exact resolve b0e1808 b0e1859
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1808 b0e1859
      have b0e1940 : y = (M.op x y) := by
        first
        | (have i₁ := b0e1923
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e1923
        | exact resolve b0e1923 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1923
      have b0e20152 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e709 X0
           have i₂ := b0e725 X0 X0
           grind)
        | exact superpose b0e725 b0e709
        | exact resolve b0e709 b0e725
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e709 b0e725
      have b0e20898 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e20152 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e20152
        | exact resolve b0e20152 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20152
      have b0e21128 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20898
           grind)
        | exact superpose b0e20898 b0e18
        | exact resolve b0e18 b0e20898
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20898
      have b0e21161 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e21128
           have i₂ := b0e1940
           grind)
        | exact superpose b0e1940 b0e21128
        | exact resolve b0e21128 b0e1940
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1940 b0e21128
      have b0e21162 : False := by grind
      exact b0e21162
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : x = (k x y) := by grind
        have b1e26 : (σ y) = (k (σ y) (σ x)) := by grind
        have b1e27 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e26
          | exact resolve b1e26 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e32 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y x)
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e13
          | exact resolve b1e13 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e33 : y = (k y x) := by
          first
          | (have i₁ := b1e32
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e32
          | exact resolve b1e32 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e37 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : ∀ X0 : G, (k X0 (M.op x (M.op y X0))) = X0 := by
          intro X0
          grind
        have b1e77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b1e91 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b1e92 : x = (M.op y y) ∨ (k y x) = (M.op y x) := by grind
        have b1e108 : x = (M.op y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e92
             have i₂ := b1e33
             grind)
          | exact superpose b1e33 b1e92
          | exact resolve b1e92 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e92
        have b1e109 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e91
             have r₂ := b1e21
             grind)
          | exact resolve b1e91 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e91
        have b1e112 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e109
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e109
          | exact resolve b1e109 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e109
        have b1e114 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e112
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e112
          | exact resolve b1e112 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e112
        have b1e116 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e114
             grind)
          | exact superpose b1e114 b1e19
          | exact resolve b1e19 b1e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e114
        have b1e136 : y = (k y (M.op x x)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e46 y
             have i₂ := b1e108
             grind)
          | exact superpose b1e108 b1e46
          | exact resolve b1e46 b1e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e139 : x = (M.op x x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e37 y
             have i₂ := b1e108
             grind)
          | exact superpose b1e108 b1e37
          | exact resolve b1e37 b1e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e108
        have b1e142 : y = (M.op y x) ∨ x = y := by
          first
          | (have i₁ := b1e139
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e139
          | exact resolve b1e139 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e139
        have b1e144 : y = (k y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e136
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e136
          | exact resolve b1e136 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e136
        have b1e1046 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e144
             grind)
          | exact superpose b1e144 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e144
        have b1e1047 : y = (M.op y y) ∨ y = (M.op y x) := by grind
        clear b1e1046
        have b1e1262 : y = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e37 y
             have i₂ := b1e1047
             grind)
          | exact superpose b1e1047 b1e37
          | exact resolve b1e37 b1e1047
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1047
        have b1e1407 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e37 x
             have i₂ := b1e1262
             grind)
          | exact superpose b1e1262 b1e37
          | exact resolve b1e37 b1e1262
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e1262
        have b1e1414 : y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e1407
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1407
          | exact resolve b1e1407 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1407
        have b1e1415 : y = (M.op x y) := by grind
        clear b1e1414
        have b1e1560 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e116
             have i₂ := b1e1415
             grind)
          | exact superpose b1e1415 b1e116
          | exact resolve b1e116 b1e1415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116
        have b1e1566 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y x
             have i₂ := b1e1415
             grind)
          | exact superpose b1e1415 b1e12
          | exact resolve b1e12 b1e1415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1415
        have b1e2232 : (M.op x x) = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b1e1566 x
             have i₂ := b1e142
             grind)
          | exact superpose b1e142 b1e1566
          | exact resolve b1e1566 b1e142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e142 b1e1566
        have b1e2335 : y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b1e2232
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e2232
          | exact resolve b1e2232 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2232
        have b1e2754 : y = (k y y) ∨ x = y := by grind
        clear b1e2335
        have b1e4442 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e77 y y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e77
          | exact resolve b1e77 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e4762 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b1e4442
        have b1e4872 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b1e4762
             have r₂ := b1e1560
             grind)
          | exact resolve b1e4762 b1e1560
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4762
        have b1e4940 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b1e4872
             have i₂ := b1e2754
             grind)
          | exact superpose b1e2754 b1e4872
          | exact resolve b1e4872 b1e2754
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2754 b1e4872
        have b1e4962 : x = y := by
          first
          | (have r₁ := b1e4940
             have r₂ := b1e1560
             grind)
          | exact resolve b1e4940 b1e1560
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4940
        have b1e5373 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e1560
             have i₂ := b1e4962
             grind)
          | exact superpose b1e4962 b1e1560
          | exact resolve b1e1560 b1e4962
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1560 b1e4962
        have b1e5381 : False := by grind
        exact b1e5381
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
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
        have b2e29 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op x (M.op y X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e29 X0
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op x (M.op y X0)) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 X0
             have i₂ := b2e29 X0
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op y X0) (M.op (M.op X0 X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (M.op y X0) x
             have i₂ := b2e29 X0
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b2e74 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e90 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e74 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e112 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        clear b2e27
        have b2e173 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e112
        have b2e190 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e173 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e173
          | exact resolve b2e173 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e173
        have b2e2589 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y x) (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e40 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e40
          | exact resolve b2e40 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e3279 : (M.op x x) = (M.op x (M.op y (M.op y x))) := by
          first
          | (have i₁ := b2e2589 x
             have i₂ := b2e29 (M.op y x)
             grind)
          | exact superpose b2e29 b2e2589
          | exact resolve b2e2589 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e3351 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op y (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b2e36 (M.op y X0) x y
             have i₂ := b2e2589 X0
             grind)
          | exact superpose b2e2589 b2e36
          | exact resolve b2e36 b2e2589
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2589
        have b2e3447 : (M.op x x) = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b2e3279
             have i₂ := b2e3351 x
             grind)
          | exact superpose b2e3351 b2e3279
          | exact resolve b2e3279 b2e3351
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3279 b2e3351
        have b2e3475 : y = (M.op x y) := by
          first
          | (have i₁ := b2e3447
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3447
          | exact resolve b2e3447 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3447
        have b2e3887 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e36 X0 y x
             have i₂ := b2e3475
             grind)
          | exact superpose b2e3475 b2e36
          | exact resolve b2e36 b2e3475
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e5120 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e66 x x
             grind)
          | exact superpose b2e66 b2e21
          | (have j1 := b2e66 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e66 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e66 x y
             grind)
          | exact resolve b2e21 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5295 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e66 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e5296 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e5295 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5295
        have b2e5331 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e5120
        have b2e5519 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e3887 (M.op (M.op x (M.op y y)) x)
             have i₂ := b2e38 y x
             grind)
          | exact superpose b2e38 b2e3887
          | exact resolve b2e3887 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e3887
        have b2e5960 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b2e5519 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5519
          | exact resolve b2e5519 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5519
        have b2e6030 : y = (M.op y y) := by
          first
          | (have i₁ := b2e5960
             have i₂ := b2e3475
             grind)
          | exact superpose b2e3475 b2e5960
          | exact resolve b2e5960 b2e3475
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3475 b2e5960
        have b2e6487 : y = (k y y) := by grind
        clear b2e6030
        have b2e17104 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e5296 y
             have i₂ := b2e6487
             grind)
          | exact superpose b2e6487 b2e5296
          | (have j0 := b2e5296 y
             grind)
          | exact resolve b2e5296 b2e6487
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5296 b2e6487
        have b2e17109 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e17104
        have b2e17151 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e17109
             grind)
          | exact superpose b2e17109 b2e22
          | exact resolve b2e22 b2e17109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17109
        have b2e17259 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e5331
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e5331
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e5331 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5331
        have b2e17268 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e17259
        have b2e17285 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17268
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e17268
          | exact resolve b2e17268 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17268
        have b2e17286 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e17285
        have b2e17297 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e17286
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e17286
          | exact resolve b2e17286 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17286
        have b2e19332 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e190 x
             have i₂ := b2e17297
             grind)
          | exact superpose b2e17297 b2e190
          | exact resolve b2e190 b2e17297
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e190 b2e17297
        have b2e19412 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e19332
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e19332
          | exact resolve b2e19332 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19332
        have b2e20050 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e90 x x
             have i₂ := b2e19412
             grind)
          | exact superpose b2e19412 b2e90
          | (have j0 := b2e90 x x
             grind)
          | exact resolve b2e90 b2e19412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90 b2e19412
        have b2e20051 : x = (M.op x x) ∨ x = y := by grind
        clear b2e20050
        have b2e20078 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e20051
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e20051
          | exact resolve b2e20051 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20051
        have b2e20079 : x = y := by grind
        clear b2e20078
        have b2e21915 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e17151
             have i₂ := b2e20079
             grind)
          | exact superpose b2e20079 b2e17151
          | exact resolve b2e17151 b2e20079
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17151 b2e20079
        have b2e21918 : False := by grind
        exact b2e21918
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e27 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e26
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e26
          | exact resolve b3e26 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e32 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e13
          | exact resolve b3e13 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e33 : x = (k x y) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e32
          | exact resolve b3e32 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e37 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b3e90 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        have b3e106 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e90
             have r₂ := b3e20
             grind)
          | exact resolve b3e90 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90
        have b3e110 : x = (M.op x y) := by
          first
          | (have i₁ := b3e106
             have i₂ := b3e33
             grind)
          | exact superpose b3e33 b3e106
          | exact resolve b3e106 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e106
        have b3e115 : (M.op y y) = (M.op y x) := by
          first
          | (have i₁ := b3e37 y
             have i₂ := b3e110
             grind)
          | exact superpose b3e110 b3e37
          | exact resolve b3e37 b3e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e117 : x = (M.op y x) := by
          first
          | (have i₁ := b3e115
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e115
          | exact resolve b3e115 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e115
        have b3e127 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x y
             have i₂ := b3e117
             grind)
          | exact superpose b3e117 b3e12
          | exact resolve b3e12 b3e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e117
        have b3e172 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b3e127 y
             have i₂ := b3e110
             grind)
          | exact superpose b3e110 b3e127
          | exact resolve b3e127 b3e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e110 b3e127
        have b3e186 : x = (M.op x x) := by
          first
          | (have i₁ := b3e172
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e172
          | exact resolve b3e172 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e172
        have b3e227 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e186
             grind)
          | exact superpose b3e186 b3e20
          | exact resolve b3e20 b3e186
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e231 : x = (k x x) := by grind
        clear b3e186
        have b3e7000 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e75 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e75
          | exact resolve b3e75 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e7364 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e7000
        have b3e7494 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e7364
             have i₂ := b3e231
             grind)
          | exact superpose b3e231 b3e7364
          | exact resolve b3e7364 b3e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e231 b3e7364
        have b3e7495 : (σ x) = (σ y) := by grind
        clear b3e7494
        have b3e7658 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e7495
             grind)
          | exact superpose b3e7495 b3e13
          | exact resolve b3e13 b3e7495
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7495
        have b3e7680 : x = y := by
          first
          | (have i₁ := b3e7658
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e7658
          | exact resolve b3e7658 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7658
        have b3e7689 : False := by grind
        exact b3e7689
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x x) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e93 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          have b4e94 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          have b4e110 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e94
               have r₂ := b4e21
               grind)
            | exact resolve b4e94 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94
          have b4e111 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e93
               have r₂ := b4e23
               grind)
            | exact resolve b4e93 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93
          have b4e114 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e111
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e111
            | exact resolve b4e111 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111
          have b4e116 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e114
               have i₂ := b4e110
               grind)
            | exact superpose b4e110 b4e114
            | exact resolve b4e114 b4e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e110 b4e114
          have b4e118 : False := by grind
          exact b4e118
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e37 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X1 (M.op X2 X3)) X0)) = (M.op X3 (M.op X0 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X1 (M.op X2 X3)) X0) X3 X2
               have i₂ := b5e13 X0 (M.op X2 X3) X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op y (M.op x X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e37 X0
               grind)
            | exact superpose b5e37 b5e13
            | exact resolve b5e13 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op x X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op x X0) y
               have i₂ := b5e37 X0
               grind)
            | exact superpose b5e37 b5e13
            | exact resolve b5e13 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b5e85 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e101 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e85 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e117 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e29 X1 X0
               grind)
            | exact superpose b5e29 b5e14
            | exact resolve b5e14 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e288 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b5e117
          have b5e305 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e288 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e288
            | exact resolve b5e288 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e288
          have b5e1669 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e48 y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e48
            | exact resolve b5e48 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e2154 : (M.op y y) = (M.op y (M.op x (M.op x y))) := by
            first
            | (have i₁ := b5e1669 y
               have i₂ := b5e37 (M.op x y)
               grind)
            | exact superpose b5e37 b5e1669
            | exact resolve b5e1669 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2210 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op x (M.op x X0))) := by
            intro X0
            first
            | (have i₁ := b5e44 (M.op x X0) y x
               have i₂ := b5e1669 X0
               grind)
            | exact superpose b5e1669 b5e44
            | exact resolve b5e44 b5e1669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2282 : (M.op y y) = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b5e2154
               have i₂ := b5e2210 y
               grind)
            | exact superpose b5e2210 b5e2154
            | exact resolve b5e2154 b5e2210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2154 b5e2210
          have b5e2301 : x = (M.op y x) := by
            first
            | (have i₁ := b5e2282
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2282
            | exact resolve b5e2282 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2282
          have b5e2652 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e2301
               grind)
            | exact superpose b5e2301 b5e13
            | exact resolve b5e13 b5e2301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2659 : ∀ X0 X1 : G, (M.op x (M.op X1 X1)) = (M.op (M.op (M.op X0 x) X1) (M.op (M.op X0 x) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e41 X0 X1 y x
               have i₂ := b5e2301
               grind)
            | exact superpose b5e2301 b5e41
            | exact resolve b5e41 b5e2301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e2661 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e44 X0 x y
               have i₂ := b5e2301
               grind)
            | exact superpose b5e2301 b5e44
            | exact resolve b5e44 b5e2301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2301
          have b5e2662 : ∀ X0 X1 : G, (M.op x (M.op X1 X1)) = (M.op y (M.op x (M.op (M.op X0 x) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2659 X0 X1
               have i₂ := b5e37 (M.op (M.op X0 x) X1)
               grind)
            | exact superpose b5e37 b5e2659
            | exact resolve b5e2659 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e2659
          have b5e2664 : ∀ X0 X1 : G, (M.op x (M.op X1 X1)) = (M.op x (M.op x (M.op (M.op X0 x) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2662 X0 X1
               have i₂ := b5e2661 (M.op (M.op X0 x) X1)
               grind)
            | exact superpose b5e2661 b5e2662
            | exact resolve b5e2662 b5e2661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2662
          have b5e2665 : ∀ X1 : G, (M.op x (M.op y (M.op x X1))) = (M.op x (M.op X1 X1)) := by
            intro X1
            first
            | (have i₁ := b5e2664 x X1
               have i₂ := b5e44 X1 x x
               grind)
            | exact superpose b5e44 b5e2664
            | exact resolve b5e2664 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e2664
          have b5e2666 : ∀ X1 : G, (M.op x (M.op X1 X1)) = (M.op x (M.op x (M.op x X1))) := by
            intro X1
            first
            | (have i₁ := b5e2665 X1
               have i₂ := b5e2661 X1
               grind)
            | exact superpose b5e2661 b5e2665
            | exact resolve b5e2665 b5e2661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2661 b5e2665
          have b5e3805 : (M.op y y) = (M.op x (M.op x (M.op x y))) := by
            first
            | (have i₁ := b5e1669 y
               have i₂ := b5e2652 (M.op x y)
               grind)
            | exact superpose b5e2652 b5e1669
            | exact resolve b5e1669 b5e2652
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1669 b5e2652
          have b5e3838 : (M.op y y) = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e3805
               have i₂ := b5e2666 y
               grind)
            | exact superpose b5e2666 b5e3805
            | exact resolve b5e3805 b5e2666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2666 b5e3805
          have b5e3864 : x = (M.op x x) := by
            first
            | (have i₁ := b5e3838
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3838
            | exact resolve b5e3838 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3838
          have b5e4369 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e3864
               grind)
            | exact superpose b5e3864 b5e21
            | exact resolve b5e21 b5e3864
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3864
          have b5e5641 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e73 y y
               grind)
            | exact superpose b5e73 b5e24
            | (have j1 := b5e73 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e73 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e73 y x
               grind)
            | exact resolve b5e24 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e5850 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e5641
          have b5e20189 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e5850
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e5850
            | (have j1 := b5e18 (σ y) (σ y)
               grind)
            | exact resolve b5e5850 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5850
          have b5e20198 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e20189
          have b5e20215 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e20198
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20198
            | exact resolve b5e20198 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20198
          have b5e20216 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e20215
          have b5e20227 : x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e20216
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20216
            | exact resolve b5e20216 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20216
          have b5e20237 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have r₁ := b5e20227
               have r₂ := b5e4369
               grind)
            | exact resolve b5e20227 b5e4369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20227
          have b5e20649 : y = (k y (τ (σ y))) := by
            first
            | (have i₁ := b5e305 y
               have i₂ := b5e20237
               grind)
            | exact superpose b5e20237 b5e305
            | exact resolve b5e305 b5e20237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e305 b5e20237
          have b5e20730 : y = (k y y) := by
            first
            | (have i₁ := b5e20649
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e20649
            | exact resolve b5e20649 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20649
          have b5e22375 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e101 y y
               have i₂ := b5e20730
               grind)
            | exact superpose b5e20730 b5e101
            | (have j0 := b5e101 y y
               grind)
            | exact resolve b5e101 b5e20730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e101 b5e20730
          have b5e22376 : y = (M.op y y) := by grind
          clear b5e22375
          have b5e22399 : x = y := by
            first
            | (have i₁ := b5e22376
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e22376
            | exact resolve b5e22376 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22376
          have b5e22419 : False := by grind
          exact b5e22419
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : (σ x) = (k (σ x) (σ y)) := by grind
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
        have b6e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b6e80 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
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
        have b6e81 : (σ x) = (σ (M.op y x)) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e80
             have r₂ := b6e20
             grind)
          | exact resolve b6e80 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e84 : (σ x) = (σ (M.op y x)) := by
          first
          | (have r₁ := b6e81
             have r₂ := b6e21
             grind)
          | exact resolve b6e81 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e88 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e102 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e88 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e7638 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e77 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e77
          | exact resolve b6e77 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e8056 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e7638
        have b6e8286 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e8056
             grind)
          | exact superpose b6e8056 b6e13
          | exact resolve b6e13 b6e8056
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e8304 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e8286
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e8286
          | exact resolve b6e8286 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8286
        have b6e8701 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e102 x x
             have i₂ := b6e8304
             grind)
          | exact superpose b6e8304 b6e102
          | (have j0 := b6e102 x y
             grind)
          | exact resolve b6e102 b6e8304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102 b6e8304
        have b6e8702 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e8701
        have b6e8708 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e8702
             have r₂ := b6e20
             grind)
          | exact resolve b6e8702 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8702
        have b6e9173 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e8708
        have b6e10306 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e8056
             have i₂ := b6e9173
             grind)
          | exact superpose b6e9173 b6e8056
          | exact resolve b6e8056 b6e9173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8056 b6e9173
        have b6e10331 : (σ x) = (σ y) := by grind
        clear b6e10306
        have b6e11117 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e10331
             grind)
          | exact superpose b6e10331 b6e19
          | exact resolve b6e19 b6e10331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e11124 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e10331
             grind)
          | exact superpose b6e10331 b6e13
          | exact resolve b6e13 b6e10331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e11146 : x = y := by
          first
          | (have i₁ := b6e11124
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e11124
          | exact resolve b6e11124 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11124
        have b6e11150 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e11117
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e11117
          | exact resolve b6e11117 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11117
        have b6e11158 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e11150
             have i₂ := b6e10331
             grind)
          | exact superpose b6e10331 b6e11150
          | exact resolve b6e11150 b6e10331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10331 b6e11150
        have b6e11165 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e11158
             have i₂ := b6e11146
             grind)
          | exact superpose b6e11146 b6e11158
          | exact resolve b6e11158 b6e11146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11158
        have b6e12175 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e84
             have i₂ := b6e11146
             grind)
          | exact superpose b6e11146 b6e84
          | exact resolve b6e84 b6e11146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84 b6e11146
        have b6e12186 : False := by grind
        exact b6e12186
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : (σ y) = (k (σ y) (σ x)) := by grind
          have b7e28 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e27
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e27
            | exact resolve b7e27 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b7e33 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e28
               grind)
            | exact superpose b7e28 b7e14
            | exact resolve b7e14 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : y = (k y x) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e33
            | exact resolve b7e33 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e38 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 X2 X2
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X2 X1) X1 X2
               have i₂ := b7e13 (M.op X2 X1) X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X1 (M.op X2 X3)) X0)) = (M.op X3 (M.op X0 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op (M.op X1 (M.op X2 X3)) X0) X3 X2
               have i₂ := b7e13 X0 (M.op X2 X3) X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b7e74 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e34
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e34
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e34 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e75 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e28
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e28 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e76 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e22
               grind)
            | exact resolve b7e75 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e77 : y = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e22
               grind)
            | exact resolve b7e74 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e79 : (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b7e76
               have r₂ := b7e21
               grind)
            | exact resolve b7e76 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e80 : y = (M.op x y) := by
            first
            | (have r₁ := b7e77
               have r₂ := b7e21
               grind)
            | exact resolve b7e77 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e82 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y x
               have i₂ := b7e80
               grind)
            | exact superpose b7e80 b7e13
            | exact resolve b7e13 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e83 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e84 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b7e86 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          have b7e96 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e84 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e97 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e83 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e98 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e86
               have r₂ := b7e23
               grind)
            | exact resolve b7e86 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e100 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e98
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e98
            | exact resolve b7e98 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e113 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e30 X1 X0
               grind)
            | exact superpose b7e30 b7e14
            | exact resolve b7e14 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e130 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e100
               grind)
            | exact superpose b7e100 b7e20
            | exact resolve b7e20 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e131 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ (k x y)) X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e100
               grind)
            | exact superpose b7e100 b7e13
            | exact resolve b7e13 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e132 : (σ y) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e130
               have i₂ := b7e79
               grind)
            | exact superpose b7e79 b7e130
            | exact resolve b7e130 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e130
          have b7e133 : (σ y) ≠ (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e132
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e132
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e132 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e132
          have b7e134 : (σ y) ≠ (σ (M.op y x)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e133
               have r₂ := b7e21
               grind)
            | exact resolve b7e133 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e133
          have b7e135 : (σ y) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b7e134
               have r₂ := b7e22
               grind)
            | exact resolve b7e134 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e134
          have b7e141 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (k x y))) := by
            first
            | (have i₁ := b7e38 (σ y)
               have i₂ := b7e100
               grind)
            | exact superpose b7e100 b7e38
            | exact resolve b7e38 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e159 : (σ x) = (M.op (σ y) (σ (k x y))) := by
            first
            | (have i₁ := b7e141
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e141
            | exact resolve b7e141 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141
          have b7e793 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b7e113
          have b7e810 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e793 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e793
            | exact resolve b7e793 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e793
          have b7e847 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (k x y)) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ (k x y)) (σ y)
               have i₂ := b7e159
               grind)
            | exact superpose b7e159 b7e13
            | exact resolve b7e13 b7e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e159
          have b7e1286 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ (M.op y x)) X0)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b7e131 X0
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e131
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e131 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1367 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ (M.op y x)) X0)) ∨ x = (M.op y y) := by
            intro X0
            first
            | (have j0 := b7e1286 X0
               grind)
            | (have r₁ := b7e1286 X0
               have r₂ := b7e21
               grind)
            | exact resolve b7e1286 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1286
          have b7e1395 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ (M.op y x)) X0)) := by
            intro X0
            first
            | (have j0 := b7e1367 X0
               grind)
            | (have r₁ := b7e1367 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e1367 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1367
          have b7e1482 : (σ y) = (σ (M.op y x)) ∨ x = (M.op y y) ∨ (k x y) = (M.op y x) := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e96 y x
               grind)
            | exact superpose b7e96 b7e28
            | (have j1 := b7e96 y x
               grind)
            | exact resolve b7e28 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e96
          have b7e1508 : x = (M.op y y) ∨ (k x y) = (M.op y x) := by
            first
            | (have r₁ := b7e1482
               have r₂ := b7e135
               grind)
            | exact resolve b7e1482 b7e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e135 b7e1482
          have b7e1532 : (k x y) = (M.op y x) := by
            first
            | (have r₁ := b7e1508
               have r₂ := b7e22
               grind)
            | exact resolve b7e1508 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1508
          have b7e1800 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e41 X0 X1 (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) x
               have i₂ := b7e39 X0 X1 (M.op X1 X0) x
               grind)
            | exact superpose b7e39 b7e41
            | exact resolve b7e41 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e41
          have b7e4450 : (M.op (σ y) (σ y)) = (M.op (σ (k x y)) (σ (k x y))) := by
            first
            | (have i₁ := b7e847 (σ y)
               have i₂ := b7e100
               grind)
            | exact superpose b7e100 b7e847
            | exact resolve b7e847 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100
          have b7e4526 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (M.op (σ x) X0) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b7e131 (M.op (σ x) X0)
               have i₂ := b7e847 X0
               grind)
            | exact superpose b7e847 b7e131
            | exact resolve b7e131 b7e847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e131 b7e847
          have b7e4553 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op y (M.op y (M.op (σ x) X0))) := by
            intro X0
            first
            | (have i₁ := b7e4526 X0
               have i₂ := b7e82 (M.op (σ x) X0)
               grind)
            | exact superpose b7e82 b7e4526
            | exact resolve b7e4526 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4526
          have b7e4623 : (M.op (σ y) (σ y)) = (M.op y (M.op y (σ (k x y)))) := by
            first
            | (have i₁ := b7e4450
               have i₂ := b7e82 (σ (k x y))
               grind)
            | exact superpose b7e82 b7e4450
            | exact resolve b7e4450 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4450
          have b7e4687 : (M.op (σ y) (σ y)) = (M.op y (M.op y (σ (M.op y x)))) := by
            first
            | (have i₁ := b7e4623
               have i₂ := b7e1532
               grind)
            | exact superpose b7e1532 b7e4623
            | exact resolve b7e4623 b7e1532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1532 b7e4623
          have b7e4703 : (σ x) = (M.op y (M.op y (σ (M.op y x)))) := by
            first
            | (have i₁ := b7e4687
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e4687
            | exact resolve b7e4687 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4687
          have b7e5089 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = (M.op (σ (M.op y x)) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e42 X0 y y (σ (M.op y x))
               have i₂ := b7e4703
               grind)
            | exact superpose b7e4703 b7e42
            | exact resolve b7e42 b7e4703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e5110 : ∀ X0 : G, (M.op y (M.op y (M.op (σ x) X0))) = (M.op (σ (M.op y x)) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e5089 X0
               have i₂ := b7e82 (M.op (σ x) X0)
               grind)
            | exact superpose b7e82 b7e5089
            | exact resolve b7e5089 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5089
          have b7e6665 : (M.op y (M.op y (σ (M.op y x)))) = (M.op (σ y) (M.op y (M.op y (σ (M.op y x))))) := by
            first
            | (have i₁ := b7e1395 (σ (M.op y x))
               have i₂ := b7e82 (σ (M.op y x))
               grind)
            | exact superpose b7e82 b7e1395
            | exact resolve b7e1395 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e6752 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op y x)) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b7e1800 (σ y) (σ (M.op y x))
               have i₂ := b7e1395 (M.op (σ y) (σ y))
               grind)
            | exact superpose b7e1395 b7e1800
            | exact resolve b7e1800 b7e1395
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1395 b7e1800
          have b7e6784 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op y (M.op y (M.op (σ x) (σ y)))) := by
            first
            | (have i₁ := b7e6752
               have i₂ := b7e5110 (σ y)
               grind)
            | exact superpose b7e5110 b7e6752
            | exact resolve b7e6752 b7e5110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5110 b7e6752
          have b7e6829 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e6665
               have i₂ := b7e4703
               grind)
            | exact superpose b7e4703 b7e6665
            | exact resolve b7e6665 b7e4703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4703 b7e6665
          have b7e6865 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ y) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b7e6784
               have i₂ := b7e4553 (σ y)
               grind)
            | exact superpose b7e4553 b7e6784
            | exact resolve b7e6784 b7e4553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4553 b7e6784
          have b7e6894 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e6865
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e6865
            | exact resolve b7e6865 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6865
          have b7e6905 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e6894
               have i₂ := b7e6829
               grind)
            | exact superpose b7e6829 b7e6894
            | exact resolve b7e6894 b7e6829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6829 b7e6894
          have b7e6928 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e72 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e72
            | exact resolve b7e72 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e7335 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e6928
          have b7e7628 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e6905
               grind)
            | exact superpose b7e6905 b7e23
            | exact resolve b7e23 b7e6905
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e7631 : x = (k x (τ (σ x))) := by
            first
            | (have i₁ := b7e810 x
               have i₂ := b7e6905
               grind)
            | exact superpose b7e6905 b7e810
            | exact resolve b7e810 b7e6905
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e810 b7e6905
          have b7e7683 : x = (k x x) := by
            first
            | (have i₁ := b7e7631
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e7631
            | exact resolve b7e7631 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7631
          have b7e8551 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e97 x x
               have i₂ := b7e7683
               grind)
            | exact superpose b7e7683 b7e97
            | (have j0 := b7e97 x x
               grind)
            | exact resolve b7e97 b7e7683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7683
          have b7e8552 : x = (M.op x x) := by grind
          clear b7e8551
          have b7e9009 : x ≠ y := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e8552
               grind)
            | exact superpose b7e8552 b7e21
            | exact resolve b7e21 b7e8552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8552
          have b7e11444 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e7335
               grind)
            | exact superpose b7e7335 b7e14
            | exact resolve b7e14 b7e7335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7335
          have b7e11466 : (τ (σ x)) = (k y y) := by
            first
            | (have r₁ := b7e11444
               have r₂ := b7e7628
               grind)
            | exact resolve b7e11444 b7e7628
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7628 b7e11444
          have b7e11487 : x = (k y y) := by
            first
            | (have i₁ := b7e11466
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e11466
            | exact resolve b7e11466 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11466
          have b7e11518 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e97 y y
               have i₂ := b7e11487
               grind)
            | exact superpose b7e11487 b7e97
            | (have j0 := b7e97 y x
               grind)
            | exact resolve b7e97 b7e11487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97
          have b7e11519 : x = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b7e11518
          have b7e11525 : y = (M.op y y) := by
            first
            | (have r₁ := b7e11519
               have r₂ := b7e22
               grind)
            | exact resolve b7e11519 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11519
          have b7e12278 : y = (k y y) := by grind
          clear b7e11525
          have b7e12324 : x = y := by
            first
            | (have i₁ := b7e12278
               have i₂ := b7e11487
               grind)
            | exact superpose b7e11487 b7e12278
            | exact resolve b7e12278 b7e11487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11487 b7e12278
          have b7e12337 : False := by grind
          exact b7e12337
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e53 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ y) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ y) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e705 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e53 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e706 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e705
               have r₂ := b8e23
               grind)
            | exact resolve b8e705 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e705
          have b8e707 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e706
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e706
            | exact resolve b8e706 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e706
          have b8e708 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e707
               grind)
            | exact superpose b8e707 b8e20
            | exact resolve b8e20 b8e707
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e707
          have b8e723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e708
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e708
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e708 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e708
          have b8e724 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e723
          have b8e727 : y = (M.op x x) := by
            first
            | (have r₁ := b8e724
               have r₂ := b8e22
               grind)
            | exact resolve b8e724 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e724
          have b8e731 : False := by grind
          exact b8e731

/-- `Equation3495`: `x ◇ x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pyx_Equation3495 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3495 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e41 : (M.op x y) = (k x y) := by grind
      have b0e42 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e46 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e42
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e42
        | exact resolve b0e42 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e47 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e46
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e46
        | exact resolve b0e46 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e46
      have b0e48 : False := by grind
      exact b0e48
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b1e28 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : (M.op x y) = (k x y) := by grind
        have b1e40 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by grind
        have b1e44 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e40
          | exact resolve b1e40 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e47 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        have b1e51 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          grind
        have b1e52 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b1e58 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e21
             grind)
          | exact resolve b1e47 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e61 : (σ x) = (σ (k x y)) := by
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
        have b1e63 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e61
          | exact resolve b1e61 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e61
        have b1e67 : (M.op x y) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op x y)
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e13
          | exact resolve b1e13 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e68 : x = (M.op x y) := by
          first
          | (have i₁ := b1e67
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e67
          | exact resolve b1e67 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e111 : (M.op y y) = (M.op y x) := by
          first
          | (have i₁ := b1e28 y
             have i₂ := b1e68
             grind)
          | exact superpose b1e68 b1e28
          | exact resolve b1e28 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e68
        have b1e113 : x = (M.op y x) := by
          first
          | (have i₁ := b1e111
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e111
          | exact resolve b1e111 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e111
        have b1e180 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (k y x))) := by
          first
          | (have i₁ := b1e29 (σ x)
             have i₂ := b1e44
             grind)
          | exact superpose b1e44 b1e29
          | exact resolve b1e29 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e200 : (σ y) = (M.op (σ x) (σ (k y x))) := by
          first
          | (have i₁ := b1e180
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e180
          | exact resolve b1e180 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e180
        have b1e228 : y = (k y x) ∨ x = y := by
          first
          | (have i₁ := b1e51 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e51
          | exact resolve b1e51 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e1077 : (k y x) = (M.op y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e52 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e52
          | exact resolve b1e52 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e1082 : x = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e1077
             have i₂ := b1e113
             grind)
          | exact superpose b1e113 b1e1077
          | exact resolve b1e1077 b1e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e113 b1e1077
        have b1e1109 : x ≠ y ∨ y = (k y x) := by grind
        clear b1e1082
        have b1e1111 : y = (k y x) := by
          first
          | (have r₁ := b1e1109
             have r₂ := b1e228
             grind)
          | exact resolve b1e1109 b1e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e228 b1e1109
        have b1e1368 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e200
             have i₂ := b1e1111
             grind)
          | exact superpose b1e1111 b1e200
          | exact resolve b1e200 b1e1111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e200
        have b1e1489 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e1368
             grind)
          | exact superpose b1e1368 b1e19
          | exact resolve b1e19 b1e1368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1495 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ x)
             have i₂ := b1e1368
             grind)
          | exact superpose b1e1368 b1e12
          | exact resolve b1e12 b1e1368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1368
        have b1e1498 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e1489
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e1489
          | exact resolve b1e1489 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63 b1e1489
        have b1e1757 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ (k y x))) := by
          first
          | (have i₁ := b1e1495 (σ x)
             have i₂ := b1e44
             grind)
          | exact superpose b1e44 b1e1495
          | exact resolve b1e1495 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e1495
        have b1e1847 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e1757
             have i₂ := b1e1111
             grind)
          | exact superpose b1e1111 b1e1757
          | exact resolve b1e1757 b1e1111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1111 b1e1757
        have b1e1878 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e1847
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e1847
          | exact resolve b1e1847 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1847
        have b1e1898 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b1e1918 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e1898
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e1898
          | exact resolve b1e1898 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1898
        have b1e1920 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e1918
             have i₂ := b1e1878
             grind)
          | exact superpose b1e1878 b1e1918
          | exact resolve b1e1918 b1e1878
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1878 b1e1918
        have b1e2009 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e1920
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e1920
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e1920 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1920
        have b1e2017 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b1e2009
        have b1e2025 : (σ x) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e2017
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e2017
          | exact resolve b1e2017 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2017
        have b1e2026 : y = (M.op y y) := by
          first
          | (have r₁ := b1e2025
             have r₂ := b1e1498
             grind)
          | exact resolve b1e2025 b1e1498
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2025
        have b1e2783 : x = y := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e2026
             grind)
          | exact superpose b1e2026 b1e20
          | exact resolve b1e20 b1e2026
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2026
        have b1e3383 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e1498
             have i₂ := b1e2783
             grind)
          | exact superpose b1e2783 b1e1498
          | exact resolve b1e1498 b1e2783
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1498 b1e2783
        have b1e3384 : False := by grind
        exact b1e3384
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
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
        have b2e27 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e12 X2 X3 X4
             have i₂ := b2e12 X2 X0 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X0 X0) X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 (M.op (M.op X2 X3) X0) X3
             have i₂ := b2e12 X0 X3 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op y (M.op x X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e12
          | exact resolve b2e12 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op y (M.op x X0)) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 X0
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e12
          | exact resolve b2e12 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op x X0) (M.op (M.op X0 X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (M.op x X0) y
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e12
          | exact resolve b2e12 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          grind
        have b2e48 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b2e84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b2e92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b2e108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e128 : ∀ X0 : G, (k X0 (M.op y (M.op x X0))) = X0 ∨ (M.op y (M.op x X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e47 X0
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e47
          | exact resolve b2e47 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47
        have b2e184 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 (M.op X4 X5)) X2) (M.op (M.op X3 (M.op X4 X5)) X2)) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) X2))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b2e12 (M.op (M.op X3 (M.op X4 X5)) X2) X5 X4
             have i₂ := b2e27 (M.op X4 X5) X3 X2 X0 X1
             grind)
          | (have i₁ := b2e12 (M.op (M.op X3 (M.op X4 X5)) X2) X5 X4
             have i₂ := b2e27 X0 X1 X2 (M.op X4 X5) X3
             grind)
          | exact superpose b2e27 b2e12
          | exact resolve b2e12 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e185 : ∀ X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 (M.op X4 X5)) X2) (M.op (M.op X3 (M.op X4 X5)) X2)) = (M.op X5 (M.op y (M.op x X2))) := by
          intro X2 X3 X4 X5
          first
          | (have i₁ := b2e184 x x X2 X3 X4 X5
             have i₂ := b2e34 X2 x x
             grind)
          | exact superpose b2e34 b2e184
          | exact resolve b2e184 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e184
        have b2e223 : ∀ X2 X3 X4 X5 : G, (M.op X5 (M.op y (M.op x X2))) = (M.op y (M.op x (M.op (M.op X3 (M.op X4 X5)) X2))) := by
          intro X2 X3 X4 X5
          first
          | (have i₁ := b2e185 X2 X3 X4 X5
             have i₂ := b2e28 (M.op (M.op X3 (M.op X4 X5)) X2)
             grind)
          | exact superpose b2e28 b2e185
          | exact resolve b2e185 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e185
        have b2e510 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op x (M.op (M.op X0 X0) X0))) := by
          intro X0
          first
          | (have i₁ := b2e28 (M.op (M.op X0 X0) X0)
             have i₂ := b2e30 X0 X0 X0 X0
             grind)
          | exact superpose b2e30 b2e28
          | exact resolve b2e28 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e1021 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e37 y X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e37
          | exact resolve b2e37 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e1227 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e48 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1256 : (M.op y y) = (M.op y (M.op x (M.op x y))) := by
          first
          | (have i₁ := b2e1021 y
             have i₂ := b2e28 (M.op x y)
             grind)
          | exact superpose b2e28 b2e1021
          | exact resolve b2e1021 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1293 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op x (M.op x X0))) := by
          intro X0
          first
          | (have i₁ := b2e34 (M.op x X0) y x
             have i₂ := b2e1021 X0
             grind)
          | exact superpose b2e1021 b2e34
          | exact resolve b2e34 b2e1021
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1021
        have b2e1352 : (M.op y y) = (M.op y (M.op y y)) := by
          first
          | (have i₁ := b2e1256
             have i₂ := b2e1293 y
             grind)
          | exact superpose b2e1293 b2e1256
          | exact resolve b2e1256 b2e1293
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1256 b2e1293
        have b2e1369 : x = (M.op y x) := by
          first
          | (have i₁ := b2e1352
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1352
          | exact resolve b2e1352 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1352
        have b2e1647 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e34 X0 x y
             have i₂ := b2e1369
             grind)
          | exact superpose b2e1369 b2e34
          | exact resolve b2e34 b2e1369
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e2809 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1647 (M.op (M.op y (M.op x x)) x)
             have i₂ := b2e35 x x
             grind)
          | exact superpose b2e35 b2e1647
          | exact resolve b2e1647 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e1647
        have b2e3283 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b2e2809 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2809
          | exact resolve b2e2809 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2809
        have b2e3336 : x = (M.op x x) := by
          first
          | (have i₁ := b2e3283
             have i₂ := b2e1369
             grind)
          | exact superpose b2e1369 b2e3283
          | exact resolve b2e3283 b2e1369
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1369 b2e3283
        have b2e3843 : (M.op x x) = (k x x) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e48 x
             have i₂ := b2e3336
             grind)
          | exact superpose b2e3336 b2e48
          | exact resolve b2e48 b2e3336
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e3867 : x = (k x x) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e3843
             have i₂ := b2e3336
             grind)
          | exact superpose b2e3336 b2e3843
          | exact resolve b2e3843 b2e3336
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3336 b2e3843
        have b2e3868 : x = (k x x) := by grind
        clear b2e3867
        have b2e4879 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e92 y y
             grind)
          | exact superpose b2e92 b2e21
          | (have j1 := b2e92 y y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e92 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e92 x y
             grind)
          | exact resolve b2e21 b2e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5037 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e92 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92
        have b2e5038 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e5037 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5037
        have b2e5072 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e4879
        have b2e8064 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op y (M.op x (M.op (M.op y (M.op x X0)) X0))) := by
          intro X0
          first
          | (have i₁ := b2e510 X0
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e510
          | exact resolve b2e510 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e510
        have b2e8173 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op X0 (M.op y (M.op x X0))) := by
          intro X0
          first
          | (have i₁ := b2e8064 X0
             have i₂ := b2e223 X0 y x X0
             grind)
          | exact superpose b2e223 b2e8064
          | exact resolve b2e8064 b2e223
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e223 b2e8064
        have b2e8787 : ∀ X0 : G, (M.op X0 (M.op y (M.op x X0))) ≠ X0 ∨ (k X0 (M.op y (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1227 X0
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e1227
          | exact resolve b2e1227 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1227
        have b2e8861 : ∀ X0 : G, (M.op y (M.op x X0)) ≠ X0 ∨ (k X0 (M.op y (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e8787 X0
             have i₂ := b2e8173 X0
             grind)
          | exact superpose b2e8173 b2e8787
          | (have j0 := b2e8787 X0
             grind)
          | exact resolve b2e8787 b2e8173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8173 b2e8787
        have b2e8878 : ∀ X0 : G, (k X0 (M.op y (M.op x X0))) = X0 := by
          intro X0
          first
          | (have j0 := b2e8861 X0
             have j1 := b2e128 X0
             grind)
          | (have r₁ := b2e8861 X0
             have r₂ := b2e128 X0
             grind)
          | exact resolve b2e8861 b2e128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e128 b2e8861
        have b2e8921 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e8878 X0
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e8878
          | exact resolve b2e8878 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e8878
        have b2e9174 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e108 X0 (M.op (σ X0) (σ X0))
             have i₂ := b2e8921 (σ X0)
             grind)
          | exact superpose b2e8921 b2e108
          | exact resolve b2e108 b2e8921
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108 b2e8921
        have b2e9178 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e9174 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e9174
          | exact resolve b2e9174 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9174
        have b2e14369 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e5038 x
             have i₂ := b2e3868
             grind)
          | exact superpose b2e3868 b2e5038
          | (have j0 := b2e5038 x
             grind)
          | exact resolve b2e5038 b2e3868
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3868 b2e5038
        have b2e14375 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e14369
        have b2e14415 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e14375
             grind)
          | exact superpose b2e14375 b2e22
          | exact resolve b2e22 b2e14375
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14375
        have b2e14502 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e5072
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e5072
          | (have j1 := b2e17 (σ y) (σ y)
             grind)
          | exact resolve b2e5072 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5072
        have b2e14511 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e14502
        have b2e14528 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e14511
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e14511
          | exact resolve b2e14511 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14511
        have b2e14529 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e14528
        have b2e14540 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e14529
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e14529
          | exact resolve b2e14529 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14529
        have b2e18900 : y = (k y (τ (σ y))) ∨ x = y := by
          first
          | (have i₁ := b2e9178 y
             have i₂ := b2e14540
             grind)
          | exact superpose b2e14540 b2e9178
          | exact resolve b2e9178 b2e14540
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9178 b2e14540
        have b2e18981 : y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e18900
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e18900
          | exact resolve b2e18900 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18900
        have b2e19828 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e84 y y
             have i₂ := b2e18981
             grind)
          | exact superpose b2e18981 b2e84
          | (have j0 := b2e84 y y
             grind)
          | exact resolve b2e84 b2e18981
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84 b2e18981
        have b2e19829 : y = (M.op y y) ∨ x = y := by grind
        clear b2e19828
        have b2e19856 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e19829
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19829
          | exact resolve b2e19829 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19829
        have b2e19857 : x = y := by grind
        clear b2e19856
        have b2e21910 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e14415
             have i₂ := b2e19857
             grind)
          | exact superpose b2e19857 b2e14415
          | exact resolve b2e14415 b2e19857
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14415 b2e19857
        have b2e21914 : False := by grind
        exact b2e21914
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b3e29 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ y) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e44 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e40
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e40
          | exact resolve b3e40 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e48 : x = (M.op y y) ∨ x = (k x y) := by grind
        have b3e58 : x = (k x y) := by
          first
          | (have r₁ := b3e48
             have r₂ := b3e20
             grind)
          | exact resolve b3e48 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e129 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b3e29 (σ y)
             have i₂ := b3e44
             grind)
          | exact superpose b3e44 b3e29
          | exact resolve b3e29 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e147 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e129
             have i₂ := b3e58
             grind)
          | exact superpose b3e58 b3e129
          | exact resolve b3e129 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e129
        have b3e152 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e147
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e147
          | exact resolve b3e147 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e147
        have b3e171 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ y)
             have i₂ := b3e152
             grind)
          | exact superpose b3e152 b3e12
          | exact resolve b3e12 b3e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e152
        have b3e777 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ (k x y))) := by
          first
          | (have i₁ := b3e171 (σ y)
             have i₂ := b3e44
             grind)
          | exact superpose b3e44 b3e171
          | exact resolve b3e171 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44 b3e171
        have b3e842 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e777
             have i₂ := b3e58
             grind)
          | exact superpose b3e58 b3e777
          | exact resolve b3e777 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58 b3e777
        have b3e864 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e842
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e842
          | exact resolve b3e842 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e842
        have b3e954 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        have b3e968 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e954
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e954
          | exact resolve b3e954 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e954
        have b3e969 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e968
             have i₂ := b3e864
             grind)
          | exact superpose b3e864 b3e968
          | exact resolve b3e968 b3e864
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e968
        have b3e1080 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e969
             grind)
          | exact superpose b3e969 b3e13
          | exact resolve b3e13 b3e969
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e969
        have b3e1082 : x = (k x x) := by
          first
          | (have i₁ := b3e1080
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1080
          | exact resolve b3e1080 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1080
        have b3e1136 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e1082
             grind)
          | exact superpose b3e1082 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e1082
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1082
        have b3e1137 : x = (M.op x x) := by grind
        clear b3e1136
        have b3e1141 : x = y := by
          first
          | (have i₁ := b3e1137
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1137
          | exact resolve b3e1137 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1137
        have b3e1440 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e1141
             grind)
          | exact superpose b3e1141 b3e19
          | exact resolve b3e19 b3e1141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1441 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e1141
             grind)
          | exact superpose b3e1141 b3e21
          | exact resolve b3e21 b3e1141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1451 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e864
             have i₂ := b3e1141
             grind)
          | exact superpose b3e1141 b3e864
          | exact resolve b3e864 b3e1141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e864 b3e1141
        have b3e1456 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e1440
             have i₂ := b3e1441
             grind)
          | exact superpose b3e1441 b3e1440
          | exact resolve b3e1440 b3e1441
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1440 b3e1441
        have b3e1457 : False := by grind
        exact b3e1457
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e34 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y X0)) := by
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
          have b4e35 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op (σ y) X0)) := by
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
          have b4e37 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 (M.op (M.op X2 X3) X0) X3
               have i₂ := b4e13 X0 X3 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op x (M.op y X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e34 X0
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op y X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op y X0) x
               have i₂ := b4e34 X0
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : (M.op y x) = (k y x) := by grind
          have b4e46 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by grind
          have b4e47 : ∀ X0 : G, (M.op (M.op x (M.op y X0)) X0) = (k (M.op x (M.op y X0)) X0) := by
            intro X0
            grind
          have b4e50 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e46
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e46
            | exact resolve b4e46 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e51 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e50
               have i₂ := b4e45
               grind)
            | exact superpose b4e45 b4e50
            | exact resolve b4e50 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e50
          have b4e149 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e34 X0
               have i₂ := b4e35 X0
               grind)
            | exact superpose b4e35 b4e34
            | exact resolve b4e34 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e698 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y (M.op (M.op X0 X0) X0))) := by
            intro X0
            first
            | (have i₁ := b4e34 (M.op (M.op X0 X0) X0)
               have i₂ := b4e37 X0 X0 X0 X0
               grind)
            | exact superpose b4e37 b4e34
            | exact resolve b4e34 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e1105 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y x) (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e44 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e44
            | exact resolve b4e44 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e1428 : (M.op x x) = (M.op x (M.op y (M.op y x))) := by
            first
            | (have i₁ := b4e1105 x
               have i₂ := b4e34 (M.op y x)
               grind)
            | exact superpose b4e34 b4e1105
            | exact resolve b4e1105 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e1466 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b4e41 (M.op y X0) x y
               have i₂ := b4e1105 X0
               grind)
            | exact superpose b4e1105 b4e41
            | exact resolve b4e41 b4e1105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e1473 : (k (M.op x x) (M.op y x)) = (M.op (M.op x x) (M.op y x)) := by grind
          clear b4e1105
          have b4e1497 : (M.op y (M.op y x)) = (k y (M.op y x)) := by
            first
            | (have i₁ := b4e1473
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1473
            | exact resolve b4e1473 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1473
          have b4e1523 : (M.op x x) = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b4e1428
               have i₂ := b4e1466 x
               grind)
            | exact superpose b4e1466 b4e1428
            | exact resolve b4e1428 b4e1466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1428 b4e1466
          have b4e1540 : y = (M.op x y) := by
            first
            | (have i₁ := b4e1523
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1523
            | exact resolve b4e1523 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1523
          have b4e1600 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e1540
               grind)
            | exact superpose b4e1540 b4e13
            | exact resolve b4e13 b4e1540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e9885 : (σ y) = (M.op x (M.op y (M.op (σ y) (σ x)))) := by
            first
            | (have i₁ := b4e698 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e698
            | exact resolve b4e698 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e698
          have b4e9940 : (σ y) = (M.op x (M.op y (σ (M.op y x)))) := by
            first
            | (have i₁ := b4e9885
               have i₂ := b4e51
               grind)
            | exact superpose b4e51 b4e9885
            | exact resolve b4e9885 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e9885
          have b4e12178 : (M.op (σ y) (σ (M.op y x))) = (k (σ y) (σ (M.op y x))) := by
            first
            | (have i₁ := b4e47 (σ (M.op y x))
               have i₂ := b4e9940
               grind)
            | exact superpose b4e9940 b4e47
            | exact resolve b4e47 b4e9940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e12205 : (M.op (σ y) (σ (M.op y x))) = (σ (k y (M.op y x))) := by
            first
            | (have i₁ := b4e12178
               have i₂ := b4e19 y (M.op y x)
               grind)
            | exact superpose b4e19 b4e12178
            | exact resolve b4e12178 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12178
          have b4e12213 : (M.op (σ y) (σ (M.op y x))) = (σ (M.op y (M.op y x))) := by
            first
            | (have i₁ := b4e12205
               have i₂ := b4e1497
               grind)
            | exact superpose b4e1497 b4e12205
            | exact resolve b4e12205 b4e1497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1497 b4e12205
          have b4e12216 : (M.op (σ y) (σ (M.op y x))) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e12213
               have i₂ := b4e1600 x
               grind)
            | exact superpose b4e1600 b4e12213
            | exact resolve b4e12213 b4e1600
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1600 b4e12213
          have b4e12218 : (σ y) = (M.op (σ y) (σ (M.op y x))) := by
            first
            | (have i₁ := b4e12216
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e12216
            | exact resolve b4e12216 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12216
          have b4e12355 : (M.op (σ x) (σ y)) = (M.op x (M.op y (σ (M.op y x)))) := by
            first
            | (have i₁ := b4e149 (σ (M.op y x))
               have i₂ := b4e12218
               grind)
            | exact superpose b4e12218 b4e149
            | exact resolve b4e149 b4e12218
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e149 b4e12218
          have b4e12384 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e12355
               have i₂ := b4e9940
               grind)
            | exact superpose b4e9940 b4e12355
            | exact resolve b4e12355 b4e9940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9940 b4e12355
          have b4e12516 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e12384
               grind)
            | exact superpose b4e12384 b4e20
            | exact resolve b4e20 b4e12384
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12384
          have b4e12543 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e12516
               have i₂ := b4e1540
               grind)
            | exact superpose b4e1540 b4e12516
            | exact resolve b4e12516 b4e1540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1540 b4e12516
          have b4e12544 : False := by grind
          exact b4e12544
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b5e33 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X2 X3 X4
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 (M.op (M.op X2 X3) X0) X3
               have i₂ := b5e13 X0 X3 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op x (M.op y X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op x (M.op y X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 X0
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op y X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op y X0) x
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e53 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            grind
          have b5e54 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            grind
          have b5e88 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b5e96 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b5e113 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e119 : ∀ X0 : G, (k X0 (M.op x (M.op y X0))) = X0 ∨ (M.op x (M.op y X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e53 X0
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e53
            | exact resolve b5e53 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e183 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 (M.op X4 X5)) X2) (M.op (M.op X3 (M.op X4 X5)) X2)) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) X2))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e13 (M.op (M.op X3 (M.op X4 X5)) X2) X5 X4
               have i₂ := b5e33 (M.op X4 X5) X3 X2 X0 X1
               grind)
            | (have i₁ := b5e13 (M.op (M.op X3 (M.op X4 X5)) X2) X5 X4
               have i₂ := b5e33 X0 X1 X2 (M.op X4 X5) X3
               grind)
            | exact superpose b5e33 b5e13
            | exact resolve b5e13 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e184 : ∀ X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 (M.op X4 X5)) X2) (M.op (M.op X3 (M.op X4 X5)) X2)) = (M.op X5 (M.op x (M.op y X2))) := by
            intro X2 X3 X4 X5
            first
            | (have i₁ := b5e183 x x X2 X3 X4 X5
               have i₂ := b5e40 X2 x x
               grind)
            | exact superpose b5e40 b5e183
            | exact resolve b5e183 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e183
          have b5e222 : ∀ X2 X3 X4 X5 : G, (M.op X5 (M.op x (M.op y X2))) = (M.op x (M.op y (M.op (M.op X3 (M.op X4 X5)) X2))) := by
            intro X2 X3 X4 X5
            first
            | (have i₁ := b5e184 X2 X3 X4 X5
               have i₂ := b5e34 (M.op (M.op X3 (M.op X4 X5)) X2)
               grind)
            | exact superpose b5e34 b5e184
            | exact resolve b5e184 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e184
          have b5e509 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y (M.op (M.op X0 X0) X0))) := by
            intro X0
            first
            | (have i₁ := b5e34 (M.op (M.op X0 X0) X0)
               have i₂ := b5e36 X0 X0 X0 X0
               grind)
            | exact superpose b5e36 b5e34
            | exact resolve b5e34 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e1019 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y x) (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e43 x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e43
            | exact resolve b5e43 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e1225 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b5e54 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e1254 : (M.op x x) = (M.op x (M.op y (M.op y x))) := by
            first
            | (have i₁ := b5e1019 x
               have i₂ := b5e34 (M.op y x)
               grind)
            | exact superpose b5e34 b5e1019
            | exact resolve b5e1019 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1291 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e40 (M.op y X0) x y
               have i₂ := b5e1019 X0
               grind)
            | exact superpose b5e1019 b5e40
            | exact resolve b5e40 b5e1019
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1019
          have b5e1350 : (M.op x x) = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b5e1254
               have i₂ := b5e1291 x
               grind)
            | exact superpose b5e1291 b5e1254
            | exact resolve b5e1254 b5e1291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1254 b5e1291
          have b5e1367 : y = (M.op x y) := by
            first
            | (have i₁ := b5e1350
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1350
            | exact resolve b5e1350 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1350
          have b5e1645 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e40 X0 y x
               have i₂ := b5e1367
               grind)
            | exact superpose b5e1367 b5e40
            | exact resolve b5e40 b5e1367
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e2573 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op x (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e1645 (M.op (M.op x (M.op y y)) x)
               have i₂ := b5e41 y x
               grind)
            | exact superpose b5e41 b5e1645
            | exact resolve b5e1645 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e1645
          have b5e3040 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b5e2573 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2573
            | exact resolve b5e2573 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2573
          have b5e3089 : y = (M.op y y) := by
            first
            | (have i₁ := b5e3040
               have i₂ := b5e1367
               grind)
            | exact superpose b5e1367 b5e3040
            | exact resolve b5e3040 b5e1367
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1367 b5e3040
          have b5e3579 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e3089
               grind)
            | exact superpose b5e3089 b5e21
            | exact resolve b5e21 b5e3089
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3089
          have b5e5145 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e96 x x
               grind)
            | exact superpose b5e96 b5e24
            | (have j1 := b5e96 x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e96 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e96 y x
               grind)
            | exact resolve b5e24 b5e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96
          have b5e5343 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e5145
          have b5e8754 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op x (M.op y (M.op (M.op x (M.op y X0)) X0))) := by
            intro X0
            first
            | (have i₁ := b5e509 X0
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e509
            | exact resolve b5e509 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e509
          have b5e8867 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op X0 (M.op x (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e8754 X0
               have i₂ := b5e222 X0 x y X0
               grind)
            | exact superpose b5e222 b5e8754
            | exact resolve b5e8754 b5e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e222 b5e8754
          have b5e9197 : ∀ X0 : G, (M.op X0 (M.op x (M.op y X0))) ≠ X0 ∨ (k X0 (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1225 X0
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e1225
            | exact resolve b5e1225 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1225
          have b5e9277 : ∀ X0 : G, (M.op x (M.op y X0)) ≠ X0 ∨ (k X0 (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e9197 X0
               have i₂ := b5e8867 X0
               grind)
            | exact superpose b5e8867 b5e9197
            | (have j0 := b5e9197 X0
               grind)
            | exact resolve b5e9197 b5e8867
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8867 b5e9197
          have b5e9295 : ∀ X0 : G, (k X0 (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have j0 := b5e9277 X0
               have j1 := b5e119 X0
               grind)
            | (have r₁ := b5e9277 X0
               have r₂ := b5e119 X0
               grind)
            | exact resolve b5e9277 b5e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e119 b5e9277
          have b5e9339 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e9295 X0
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e9295
            | exact resolve b5e9295 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e9295
          have b5e9508 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e113 X0 (M.op (σ X0) (σ X0))
               have i₂ := b5e9339 (σ X0)
               grind)
            | exact superpose b5e9339 b5e113
            | exact resolve b5e113 b5e9339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113 b5e9339
          have b5e9512 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e9508 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e9508
            | exact resolve b5e9508 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9508
          have b5e14397 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e5343
               have i₂ := b5e18 x x
               grind)
            | exact superpose b5e18 b5e5343
            | (have j1 := b5e18 (σ x) (σ x)
               grind)
            | exact resolve b5e5343 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5343
          have b5e14406 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e14397
          have b5e14423 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e14406
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e14406
            | exact resolve b5e14406 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14406
          have b5e14424 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e14423
          have b5e14435 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e14424
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e14424
            | exact resolve b5e14424 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14424
          have b5e14445 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b5e14435
               have r₂ := b5e3579
               grind)
            | exact resolve b5e14435 b5e3579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14435
          have b5e14648 : x = (k x (τ (σ x))) := by
            first
            | (have i₁ := b5e9512 x
               have i₂ := b5e14445
               grind)
            | exact superpose b5e14445 b5e9512
            | exact resolve b5e9512 b5e14445
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9512 b5e14445
          have b5e14729 : x = (k x x) := by
            first
            | (have i₁ := b5e14648
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e14648
            | exact resolve b5e14648 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14648
          have b5e14841 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e88 x x
               have i₂ := b5e14729
               grind)
            | exact superpose b5e14729 b5e88
            | (have j0 := b5e88 x x
               grind)
            | exact resolve b5e88 b5e14729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88 b5e14729
          have b5e14842 : x = (M.op x x) := by grind
          clear b5e14841
          have b5e15262 : x = y := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e14842
               grind)
            | exact superpose b5e14842 b5e22
            | exact resolve b5e22 b5e14842
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14842
          have b5e15316 : False := by grind
          exact b5e15316
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e53 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b6e54 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X0 X1)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0 X1
          grind
        have b6e79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b6e86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e627 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e53 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e861 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e54 X0 X0 X0
             have i₂ := b6e55 X0 X0
             grind)
          | exact superpose b6e55 b6e54
          | (have j0 := b6e54 X0 x x
             have j1 := b6e55 X0 x
             grind)
          | exact resolve b6e54 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54 b6e55
        have b6e888 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e861 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e861
        have b6e893 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e888 X0
             have j1 := b6e627 X0
             grind)
          | (have r₁ := b6e888 X0
             have r₂ := b6e627 X0
             grind)
          | exact resolve b6e888 b6e627
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e627 b6e888
        have b6e940 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e893 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e893
          | exact resolve b6e893 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e946 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e940
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e940
          | exact resolve b6e940 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e940
        have b6e1014 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e946
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e946
          | (have j1 := b6e17 y x
             grind)
          | exact resolve b6e946 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e946
        have b6e1025 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e1014
             have r₂ := b6e21
             grind)
          | exact resolve b6e1014 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1014
        have b6e1027 : (σ (M.op x y)) = (σ y) := by
          first
          | (have r₁ := b6e1025
             have r₂ := b6e20
             grind)
          | exact resolve b6e1025 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1025
        have b6e5196 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e86 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e86
          | exact resolve b6e86 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e5567 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e5196
        have b6e6625 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e5567
             grind)
          | exact superpose b6e5567 b6e13
          | exact resolve b6e13 b6e5567
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e6642 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e6625
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e6625
          | exact resolve b6e6625 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6625
        have b6e7051 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e79 y y
             have i₂ := b6e6642
             grind)
          | exact superpose b6e6642 b6e79
          | (have j0 := b6e79 y x
             grind)
          | exact resolve b6e79 b6e6642
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79 b6e6642
        have b6e7055 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e7051
        have b6e7064 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e7055
             have r₂ := b6e20
             grind)
          | exact resolve b6e7055 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7055
        have b6e7505 : y = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e893 y
             have i₂ := b6e7064
             grind)
          | exact superpose b6e7064 b6e893
          | exact resolve b6e893 b6e7064
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e893 b6e7064
        have b6e8551 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e5567
             have i₂ := b6e7505
             grind)
          | exact superpose b6e7505 b6e5567
          | exact resolve b6e5567 b6e7505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5567 b6e7505
        have b6e8576 : (σ x) = (σ y) := by grind
        clear b6e8551
        have b6e8859 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e8576
             grind)
          | exact superpose b6e8576 b6e19
          | exact resolve b6e19 b6e8576
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e8888 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e8859
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e8859
          | exact resolve b6e8859 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8859
        have b6e8896 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e8888
             have i₂ := b6e8576
             grind)
          | exact superpose b6e8576 b6e8888
          | exact resolve b6e8888 b6e8576
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8576 b6e8888
        have b6e8904 : False := by
          have f8904_13 : (σ (M.op x y)) ≠ (σ y) := by grind
          have f8904_14 : (σ (M.op x y)) = (σ y) := by grind
          have f8904_27 : False := by
            first
            | (have r₁ := f8904_13
               have r₂ := f8904_14
               grind)
            | exact resolve f8904_13 f8904_14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          exact f8904_27
        exact b6e8904
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e34 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 X2 X2
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X2 X1) X1 X2
               have i₂ := b7e13 (M.op X2 X1) X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X1 (M.op X2 X3)) X0)) = (M.op X3 (M.op X0 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op (M.op X1 (M.op X2 X3)) X0) X3 X2
               have i₂ := b7e13 X0 (M.op X2 X3) X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e47 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by grind
          have b7e50 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e47
            | exact resolve b7e47 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e51 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op (σ (k y x)) X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ y)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e13
            | exact resolve b7e13 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e52 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          have b7e56 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            grind
          have b7e57 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e58 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X0 X1)) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0 X1
            grind
          have b7e60 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e52
               have r₂ := b7e23
               grind)
            | exact resolve b7e52 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
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
          have b7e88 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b7e96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b7e104 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
          have b7e105 : x = (M.op y x) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e104
               have r₂ := b7e21
               grind)
            | exact resolve b7e104 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104
          have b7e107 : x = (M.op y x) := by
            first
            | (have r₁ := b7e105
               have r₂ := b7e22
               grind)
            | exact resolve b7e105 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e113 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (k y x))) := by
            first
            | (have i₁ := b7e34 (σ x)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e34
            | exact resolve b7e34 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e126 : (σ y) = (M.op (σ x) (σ (k y x))) := by
            first
            | (have i₁ := b7e113
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e113
            | exact resolve b7e113 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113
          have b7e127 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e107
               grind)
            | exact superpose b7e107 b7e13
            | exact resolve b7e13 b7e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e107
          have b7e744 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (k y x)) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ (k y x)) (σ x)
               have i₂ := b7e126
               grind)
            | exact superpose b7e126 b7e13
            | exact resolve b7e13 b7e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e126
          have b7e877 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b7e56 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e1310 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e57 X0 X0 X0
               have i₂ := b7e58 X0 X0
               grind)
            | exact superpose b7e58 b7e57
            | (have j0 := b7e57 X0 x x
               have j1 := b7e58 X0 x
               grind)
            | exact resolve b7e57 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57 b7e58
          have b7e1339 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b7e1310 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1310
          have b7e1355 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b7e1339 X0
               have j1 := b7e877 X0
               grind)
            | (have r₁ := b7e1339 X0
               have r₂ := b7e877 X0
               grind)
            | exact resolve b7e1339 b7e877
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e877 b7e1339
          have b7e2220 : (M.op (σ x) (σ x)) = (M.op (σ (k y x)) (σ (k y x))) := by
            first
            | (have i₁ := b7e744 (σ x)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e744
            | exact resolve b7e744 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e2276 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (σ x) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e51 (M.op (σ y) X0)
               have i₂ := b7e744 X0
               grind)
            | exact superpose b7e744 b7e51
            | exact resolve b7e51 b7e744
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e744
          have b7e2289 : ∀ X0 : G, (M.op x (M.op x (M.op (σ y) X0))) = (M.op (σ x) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e2276 X0
               have i₂ := b7e127 (M.op (σ y) X0)
               grind)
            | exact superpose b7e127 b7e2276
            | exact resolve b7e2276 b7e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2276
          have b7e2331 : (M.op (σ x) (σ x)) = (M.op x (M.op x (σ (k y x)))) := by
            first
            | (have i₁ := b7e2220
               have i₂ := b7e127 (σ (k y x))
               grind)
            | exact superpose b7e127 b7e2220
            | exact resolve b7e2220 b7e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2220
          have b7e2367 : (σ y) = (M.op x (M.op x (σ (k y x)))) := by
            first
            | (have i₁ := b7e2331
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2331
            | exact resolve b7e2331 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2331
          have b7e2455 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            by_contra hcon
            push Not at hcon
            have f2455_14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
              intro X0 X1 X2 X3
              grind
            have f2455_15 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)) := by
              intro X0 X1 X2 X3
              grind
            have f2455_26 : (M.op X1 (M.op X0 X0)) ≠ (M.op X0 (M.op X1 (M.op X0 X0))) := by grind
            have f2455_207 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
              intro X0 X1
              first
              | (have i₁ := f2455_14 X0 X1 (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) x
                 have i₂ := f2455_15 X0 X1 (M.op X1 X0) x
                 grind)
              | exact superpose f2455_15 f2455_14
              | exact resolve f2455_14 f2455_15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2455_283 : (M.op X1 (M.op X0 X0)) ≠ (M.op X1 (M.op X0 X0)) := by
              first
              | (have i₁ := f2455_26
                 have i₂ := f2455_207 X0 X1
                 grind)
              | exact superpose f2455_207 f2455_26
              | (have r₁ := f2455_26
                 have r₂ := f2455_207 X0 X1
                 grind)
              | exact resolve f2455_26 f2455_207
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2455_284 : False := by grind
            exact f2455_284
          clear b7e35 b7e37
          have b7e2730 : ∀ X0 : G, (M.op (σ (k y x)) (M.op X0 X0)) = (M.op (M.op (σ y) X0) (M.op (σ y) X0)) := by
            intro X0
            by_contra hcon
            push Not at hcon
            have f2730_14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X1 (M.op X2 X3)) X0)) = (M.op X3 (M.op X0 X0)) := by
              intro X0 X1 X2 X3
              grind
            have f2730_15 : (σ y) = (M.op x (M.op x (σ (k y x)))) := by grind
            have f2730_16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              grind
            have f2730_17 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have f2730_19 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have f2730_20 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have f2730_21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have f2730_22 : x ≠ (M.op y y) := by grind
            have f2730_23 : y ≠ (M.op x x) := by grind
            have f2730_24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
            have f2730_25 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have f2730_26 : (M.op (σ (k y x)) (M.op X0 X0)) ≠ (M.op (M.op (σ y) X0) (M.op (σ y) X0)) := by grind
            have f2730_40 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            have f2730_46 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := f2730_40
                 have r₂ := f2730_24
                 grind)
              | exact resolve f2730_40 f2730_24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2730_48 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := f2730_46
                 have i₂ := f2730_21 x y
                 grind)
              | exact superpose f2730_21 f2730_46
              | exact resolve f2730_46 f2730_21
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2730_51 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := f2730_17 (k x y)
                 have i₂ := f2730_48
                 grind)
              | exact superpose f2730_48 f2730_17
              | exact resolve f2730_17 f2730_48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2730_52 : x = (k x y) := by
              first
              | (have i₁ := f2730_51
                 have i₂ := f2730_17 x
                 grind)
              | exact superpose f2730_17 f2730_51
              | exact resolve f2730_51 f2730_17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2730_92 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
              first
              | (have i₁ := f2730_20 x y
                 have i₂ := f2730_52
                 grind)
              | exact superpose f2730_52 f2730_20
              | (have j0 := f2730_20 x y
                 grind)
              | exact resolve f2730_20 f2730_52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2730_93 : x = (M.op y x) ∨ y = (M.op x x) := by
              first
              | (have r₁ := f2730_92
                 have r₂ := f2730_22
                 grind)
              | exact resolve f2730_92 f2730_22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2730_95 : x = (M.op y x) := by
              first
              | (have r₁ := f2730_93
                 have r₂ := f2730_23
                 grind)
              | exact resolve f2730_93 f2730_23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2730_99 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x X0)) := by
              intro X0
              first
              | (have i₁ := f2730_16 X0 x y
                 have i₂ := f2730_95
                 grind)
              | exact superpose f2730_95 f2730_16
              | exact resolve f2730_16 f2730_95
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2730_115 : ∀ X0 : G, (M.op (σ (k y x)) (M.op X0 X0)) = (M.op (M.op (σ y) X0) (M.op (σ y) X0)) := by
              intro X0
              first
              | (have i₁ := f2730_14 X0 x x (σ (k y x))
                 have i₂ := f2730_15
                 grind)
              | exact superpose f2730_15 f2730_14
              | exact resolve f2730_14 f2730_15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2730_141 : ∀ X0 : G, (M.op (σ (k y x)) (M.op X0 X0)) = (M.op x (M.op x (M.op (σ y) X0))) := by
              intro X0
              first
              | (have i₁ := f2730_115 X0
                 have i₂ := f2730_99 (M.op (σ y) X0)
                 grind)
              | exact superpose f2730_99 f2730_115
              | exact resolve f2730_115 f2730_99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2730_186 : (M.op (σ (k y x)) (M.op X0 X0)) ≠ (M.op x (M.op x (M.op (σ y) X0))) := by
              first
              | (have i₁ := f2730_26
                 have i₂ := f2730_99 (M.op (σ y) X0)
                 grind)
              | exact superpose f2730_99 f2730_26
              | exact resolve f2730_26 f2730_99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2730_193 : False := by
              first
              | (have r₁ := f2730_186
                 have r₂ := f2730_141 X0
                 grind)
              | exact resolve f2730_186 f2730_141
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            exact f2730_193
          clear b7e38 b7e2367
          have b7e2861 : ∀ X0 : G, (M.op (σ (k y x)) (M.op X0 X0)) = (M.op x (M.op x (M.op (σ y) X0))) := by
            intro X0
            first
            | (have i₁ := b7e2730 X0
               have i₂ := b7e127 (M.op (σ y) X0)
               grind)
            | exact superpose b7e127 b7e2730
            | exact resolve b7e2730 b7e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e127 b7e2730
          have b7e4995 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (σ (k y x)) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e51 (M.op (σ x) (σ x))
               have i₂ := b7e2455 (σ x) (σ (k y x))
               grind)
            | exact superpose b7e2455 b7e51
            | exact resolve b7e51 b7e2455
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51 b7e2455
          have b7e4999 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op x (M.op x (M.op (σ y) (σ x)))) := by
            first
            | (have i₁ := b7e4995
               have i₂ := b7e2861 (σ x)
               grind)
            | exact superpose b7e2861 b7e4995
            | exact resolve b7e4995 b7e2861
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2861 b7e4995
          have b7e5052 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e4999
               have i₂ := b7e2289 (σ x)
               grind)
            | exact superpose b7e2289 b7e4999
            | exact resolve b7e4999 b7e2289
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2289 b7e4999
          have b7e5072 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e5052
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e5052
            | exact resolve b7e5052 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5052
          have b7e5545 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e5072
               grind)
            | exact superpose b7e5072 b7e23
            | exact resolve b7e23 b7e5072
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5072
          have b7e6690 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e96 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e96
            | exact resolve b7e96 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e7091 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e6690
          have b7e7777 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e7091
               grind)
            | exact superpose b7e7091 b7e14
            | exact resolve b7e14 b7e7091
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e7799 : y = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e7777
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e7777
            | exact resolve b7e7777 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7777
          have b7e8228 : y = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e88 x x
               have i₂ := b7e7799
               grind)
            | exact superpose b7e7799 b7e88
            | (have j0 := b7e88 x y
               grind)
            | exact resolve b7e88 b7e7799
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88 b7e7799
          have b7e8232 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
          clear b7e8228
          have b7e8241 : x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e8232
               have r₂ := b7e22
               grind)
            | exact resolve b7e8232 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8232
          have b7e8696 : x = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e1355 x
               have i₂ := b7e8241
               grind)
            | exact superpose b7e8241 b7e1355
            | exact resolve b7e1355 b7e8241
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1355 b7e8241
          have b7e9649 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e7091
               have i₂ := b7e8696
               grind)
            | exact superpose b7e8696 b7e7091
            | exact resolve b7e7091 b7e8696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7091 b7e8696
          have b7e9674 : (σ x) = (σ y) := by grind
          clear b7e9649
          have b7e10448 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e5545
               have i₂ := b7e9674
               grind)
            | exact superpose b7e9674 b7e5545
            | exact resolve b7e5545 b7e9674
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5545
          have b7e10474 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e10448
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e10448
            | exact resolve b7e10448 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10448
          have b7e10486 : False := by grind
          exact b7e10486
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e91 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ x)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (M.op (σ x) (σ x)) x
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1268 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e91 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e1269 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e1268
               have r₂ := b8e23
               grind)
            | exact resolve b8e1268 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1268
          have b8e1270 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e1269
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e1269
            | exact resolve b8e1269 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1269
          have b8e1271 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1270
               grind)
            | exact superpose b8e1270 b8e20
            | exact resolve b8e20 b8e1270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1270
          have b8e1415 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e1271
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1271
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e1271 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1271
          have b8e1425 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e1415
          have b8e1432 : x = (M.op y y) := by
            first
            | (have r₁ := b8e1425
               have r₂ := b8e22
               grind)
            | exact resolve b8e1425 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1425
          have b8e1436 : False := by grind
          exact b8e1436

/-- `Equation3499`: `x ◇ x = y ◇ ((z ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation3499 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3499 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3499.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op x x) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
      have b0e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e55 (σ X0)
           grind)
        | exact superpose b0e55 b0e17
        | exact resolve b0e17 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e64 X0
           have i₂ := b0e55 X0
           grind)
        | exact superpose b0e55 b0e64
        | exact resolve b0e64 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55 b0e64
      have b0e270 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e67 x
           grind)
        | exact superpose b0e67 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e67 x
           grind)
        | exact resolve b0e22 b0e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e67
      have b0e281 : False := by grind
      exact b0e281
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x x
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e66 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e68 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e66
        have b1e70 : (k x y) = (M.op y y) := by grind
        clear b1e62
        have b1e71 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e68
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e68
          | exact resolve b1e68 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e74 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e71
             have i₂ := b1e67 y
             grind)
          | exact superpose b1e67 b1e71
          | exact resolve b1e71 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e67 (σ X0)
             grind)
          | exact superpose b1e67 b1e18
          | exact resolve b1e18 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e76 X0
             have i₂ := b1e67 X0
             grind)
          | exact superpose b1e67 b1e76
          | exact resolve b1e76 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67 b1e76
        have b1e90 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 X0 (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e92 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e90 X0
             have i₂ := b1e74
             grind)
          | exact superpose b1e74 b1e90
          | (have j0 := b1e90 X0
             grind)
          | exact resolve b1e90 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e90
        have b1e173 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e74
             grind)
          | exact superpose b1e74 b1e23
          | exact resolve b1e23 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e6687 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e92 (σ x)
             have i₂ := b1e74
             grind)
          | exact superpose b1e74 b1e92
          | (have j0 := b1e92 (σ x)
             grind)
          | (have r₁ := b1e92 (σ x)
             have r₂ := b1e74
             grind)
          | exact resolve b1e92 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74 b1e92
        have b1e6688 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e6687
        have b1e6689 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e6688
             have i₂ := b1e81 x
             grind)
          | exact superpose b1e81 b1e6688
          | exact resolve b1e6688 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6688
        have b1e6690 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e6689
             have r₂ := b1e173
             grind)
          | exact resolve b1e6689 b1e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6689
        have b1e6691 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e6690
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e6690
          | exact resolve b1e6690 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6690
        have b1e6692 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e6691
             have i₂ := b1e70
             grind)
          | exact superpose b1e70 b1e6691
          | exact resolve b1e6691 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70 b1e6691
        have b1e6693 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e6692
             have i₂ := b1e81 x
             grind)
          | exact superpose b1e81 b1e6692
          | exact resolve b1e6692 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81 b1e6692
        have b1e6694 : False := by grind
        exact b1e6694
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e59 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x x
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e65 : (k x y) = (M.op y y) := by grind
        clear b2e59
        have b2e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e63 (σ X0)
             grind)
          | exact superpose b2e63 b2e18
          | exact resolve b2e18 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e69 X0
             have i₂ := b2e63 X0
             grind)
          | exact superpose b2e63 b2e69
          | exact resolve b2e69 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63 b2e69
        have b2e133 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ y) (σ y)
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e407 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e74 y
             grind)
          | exact superpose b2e74 b2e22
          | exact resolve b2e22 b2e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e10186 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e133 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e133
        have b2e10187 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e10186
             have r₂ := b2e21
             grind)
          | exact resolve b2e10186 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10186
        have b2e10189 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e10187
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e10187
          | exact resolve b2e10187 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10187
        have b2e10191 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e10189
             have i₂ := b2e65
             grind)
          | exact superpose b2e65 b2e10189
          | exact resolve b2e10189 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65 b2e10189
        have b2e10192 : False := by grind
        exact b2e10192
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op y y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e64 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) (σ x)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e66 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e64
        have b3e69 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e66
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e66
          | exact resolve b3e66 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e65 (σ X0)
             grind)
          | exact superpose b3e65 b3e18
          | exact resolve b3e18 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e75 X0
             have i₂ := b3e65 X0
             grind)
          | exact superpose b3e65 b3e75
          | exact resolve b3e75 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e84 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e190 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e69
             grind)
          | exact superpose b3e69 b3e15
          | exact resolve b3e15 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e69
        have b3e191 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e190
        have b3e192 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e191
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e191
          | exact resolve b3e191 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e191
        have b3e193 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e192
             have i₂ := b3e65 y
             grind)
          | exact superpose b3e65 b3e192
          | exact resolve b3e192 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65 b3e192
        have b3e194 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e193
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e193
          | exact resolve b3e193 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e193
        have b3e774 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e78 x
             grind)
          | exact superpose b3e78 b3e23
          | exact resolve b3e23 b3e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e78
        have b3e2345 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e84 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e2346 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e2345
             have r₂ := b3e20
             grind)
          | exact resolve b3e2345 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2345
        have b3e2351 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e194
             have i₂ := b3e2346
             grind)
          | exact superpose b3e2346 b3e194
          | exact resolve b3e194 b3e2346
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e194 b3e2346
        have b3e2355 : False := by grind
        exact b3e2355
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e76 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e78 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e76
          have b4e81 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e78
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e78
            | exact resolve b4e78 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e86 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e81
               have i₂ := b4e77 y
               grind)
            | exact superpose b4e77 b4e81
            | exact resolve b4e81 b4e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77 b4e81
          have b4e87 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e86
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e86
            | exact resolve b4e86 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e86
          have b4e88 : False := by grind
          exact b4e88
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e81 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e73 (σ X0)
               grind)
            | exact superpose b5e73 b5e19
            | exact resolve b5e19 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e86 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e81 X0
               have i₂ := b5e73 X0
               grind)
            | exact superpose b5e73 b5e81
            | exact resolve b5e81 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73 b5e81
          have b5e93 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e170 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ y) (σ y)
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2833 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e93 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93
          have b5e2834 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e2833
               have r₂ := b5e21
               grind)
            | exact resolve b5e2833 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2833
          have b5e11826 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e170 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e170
          have b5e11827 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e11826
               have r₂ := b5e23
               grind)
            | exact resolve b5e11826 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11826
          have b5e11829 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e11827
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e11827
            | exact resolve b5e11827 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11827
          have b5e11831 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e11829
               have i₂ := b5e2834
               grind)
            | exact superpose b5e2834 b5e11829
            | exact resolve b5e11829 b5e2834
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2834 b5e11829
          have b5e11834 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e11831
               grind)
            | exact superpose b5e11831 b5e23
            | exact resolve b5e23 b5e11831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11831
          have b5e11842 : False := by grind
          exact b5e11842
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e62 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) (σ x)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e64 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e62
        have b6e66 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e64
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e64
          | exact resolve b6e64 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e94 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e66
             grind)
          | exact superpose b6e66 b6e15
          | exact resolve b6e15 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e95 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e94
        have b6e96 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e95
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e95
          | exact resolve b6e95 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e97 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e96
             have i₂ := b6e63 y
             grind)
          | exact superpose b6e63 b6e96
          | exact resolve b6e96 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63 b6e96
        have b6e173 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e97
             grind)
          | exact superpose b6e97 b6e13
          | exact resolve b6e13 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e174 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e173
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e173
          | exact resolve b6e173 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e173
        have b6e258 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e174
             grind)
          | exact superpose b6e174 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e174
        have b6e259 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e258
        have b6e261 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e259
             have r₂ := b6e21
             grind)
          | exact resolve b6e259 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e259
        have b6e263 : False := by grind
        exact b6e263
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e74 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e76 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e74
          have b7e78 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e76
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e76
            | exact resolve b7e76 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e81 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e78
               have i₂ := b7e75 y
               grind)
            | exact superpose b7e75 b7e78
            | exact resolve b7e78 b7e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e83 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e75 (σ X0)
               grind)
            | exact superpose b7e75 b7e19
            | exact resolve b7e19 b7e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e90 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e83 X0
               have i₂ := b7e75 X0
               grind)
            | exact superpose b7e75 b7e83
            | exact resolve b7e83 b7e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75 b7e83
          have b7e101 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e17 X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 X0 (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e103 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e101 X0
               have i₂ := b7e81
               grind)
            | exact superpose b7e81 b7e101
            | (have j0 := b7e101 X0
               grind)
            | exact resolve b7e101 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e109 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e81
               grind)
            | exact superpose b7e81 b7e23
            | exact resolve b7e23 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e113 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e109
               have i₂ := b7e90 x
               grind)
            | exact superpose b7e90 b7e109
            | exact resolve b7e109 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e109
          have b7e143 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e16 X0 X1
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e16 X0 X0
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X0 X0
               have j1 := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X1 X1
               have r₂ := b7e18 X1 X1
               grind)
            | (have r₁ := b7e16 X0 X0
               have r₂ := b7e18 X0 X0
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e169 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e143
          have b7e6940 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e103 (σ x)
               have i₂ := b7e81
               grind)
            | exact superpose b7e81 b7e103
            | (have j0 := b7e103 (σ x)
               grind)
            | (have r₁ := b7e103 (σ x)
               have r₂ := b7e81
               grind)
            | exact resolve b7e103 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81 b7e103
          have b7e6941 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e6940
          have b7e6942 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e6941
               have i₂ := b7e90 x
               grind)
            | exact superpose b7e90 b7e6941
            | exact resolve b7e6941 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6941
          have b7e6943 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e6942
               have r₂ := b7e113
               grind)
            | exact resolve b7e6942 b7e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6942
          have b7e6944 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e6943
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e6943
            | exact resolve b7e6943 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6943
          have b7e6945 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e6944
               have i₂ := b7e90 x
               grind)
            | exact superpose b7e90 b7e6944
            | exact resolve b7e6944 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90 b7e6944
          have b7e6947 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e6945
               have i₂ := b7e169 x y
               grind)
            | exact superpose b7e169 b7e6945
            | (have j1 := b7e169 x y
               grind)
            | exact resolve b7e6945 b7e169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e169
          have b7e6954 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e6945
               grind)
            | exact superpose b7e6945 b7e14
            | exact resolve b7e14 b7e6945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6945
          have b7e6955 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e6954
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e6954
            | exact resolve b7e6954 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6954
          have b7e6962 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e6947
               have r₂ := b7e113
               grind)
            | exact resolve b7e6947 b7e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113 b7e6947
          have b7e6966 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e6962
               have r₂ := b7e22
               grind)
            | exact resolve b7e6962 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6962
          have b7e6968 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e6966
               have i₂ := b7e6955
               grind)
            | exact superpose b7e6955 b7e6966
            | exact resolve b7e6966 b7e6955
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6955 b7e6966
          have b7e6969 : False := by grind
          exact b7e6969
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e159 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ y) (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e10512 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e159 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e159
          have b8e10513 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e10512
               have r₂ := b8e23
               grind)
            | exact resolve b8e10512 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10512
          have b8e10515 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e10513
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e10513
            | exact resolve b8e10513 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10513
          have b8e10521 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e10515
               grind)
            | exact superpose b8e10515 b8e20
            | exact resolve b8e20 b8e10515
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10515
          have b8e10680 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e10521
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e10521
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e10521 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10521
          have b8e10684 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e10680
          have b8e10687 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e10684
               have r₂ := b8e21
               grind)
            | exact resolve b8e10684 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10684
          have b8e10689 : False := by grind
          exact b8e10689

/-- `Equation3499`: `x ◇ x = y ◇ ((z ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_pyy_pxy_Equation3499 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3499 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3499.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op y y) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
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
      have b0e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e55 (σ X0)
           grind)
        | exact superpose b0e55 b0e17
        | exact resolve b0e17 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e66 X0
           have i₂ := b0e55 X0
           grind)
        | exact superpose b0e55 b0e66
        | exact resolve b0e66 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55 b0e66
      have b0e353 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e69 y
           grind)
        | exact superpose b0e69 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e69 y
           grind)
        | exact resolve b0e22 b0e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e69
      have b0e367 : False := by grind
      exact b0e367
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op y y) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e58 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 y y
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e68 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
        clear b1e62
        have b1e70 : (M.op x x) = (k x y) := by grind
        clear b1e58
        have b1e73 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e68
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e68
          | exact resolve b1e68 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e76 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e73
             have i₂ := b1e67 x
             grind)
          | exact superpose b1e67 b1e73
          | exact resolve b1e73 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e67 (σ X0)
             grind)
          | exact superpose b1e67 b1e18
          | exact resolve b1e18 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e78 X0
             have i₂ := b1e67 X0
             grind)
          | exact superpose b1e67 b1e78
          | exact resolve b1e78 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67 b1e78
        have b1e90 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e16 (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) X0
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e94 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e90 X0
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e90
          | (have j0 := b1e90 X0
             grind)
          | exact resolve b1e90 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e90
        have b1e206 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e23
          | exact resolve b1e23 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e4821 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e94 (σ y)
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e94
          | (have j0 := b1e94 (σ y)
             grind)
          | (have r₁ := b1e94 (σ y)
             have r₂ := b1e76
             grind)
          | exact resolve b1e94 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76 b1e94
        have b1e4832 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e4821
        have b1e4833 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e4832
             have i₂ := b1e83 y
             grind)
          | exact superpose b1e83 b1e4832
          | exact resolve b1e4832 b1e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4832
        have b1e4834 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e4833
             have r₂ := b1e206
             grind)
          | exact resolve b1e4833 b1e206
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4833
        have b1e4835 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e4834
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e4834
          | exact resolve b1e4834 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4834
        have b1e4836 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e4835
             have i₂ := b1e70
             grind)
          | exact superpose b1e70 b1e4835
          | exact resolve b1e4835 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70 b1e4835
        have b1e4837 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e4836
             have i₂ := b1e83 y
             grind)
          | exact superpose b1e83 b1e4836
          | exact resolve b1e4836 b1e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e83 b1e4836
        have b1e4838 : False := by grind
        exact b1e4838
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e56 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b2e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e65 : (M.op x x) = (k x y) := by grind
        clear b2e56
        have b2e71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e63 (σ X0)
             grind)
          | exact superpose b2e63 b2e18
          | exact resolve b2e18 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e71 X0
             have i₂ := b2e63 X0
             grind)
          | exact superpose b2e63 b2e71
          | exact resolve b2e71 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63 b2e71
        have b2e125 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) (σ x)
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
        have b2e774 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e76 x
             grind)
          | exact superpose b2e76 b2e22
          | exact resolve b2e22 b2e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e6568 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e125 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e125
        have b2e6569 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e6568
             have r₂ := b2e21
             grind)
          | exact resolve b2e6568 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6568
        have b2e6571 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e6569
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e6569
          | exact resolve b2e6569 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6569
        have b2e6573 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e6571
             have i₂ := b2e65
             grind)
          | exact superpose b2e65 b2e6571
          | exact resolve b2e6571 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65 b2e6571
        have b2e6574 : False := by grind
        exact b2e6574
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b3e21 : (M.op x y) = (M.op x x) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e59 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ y) (σ y)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e66 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e59
        have b3e72 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e66
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e66
          | exact resolve b3e66 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e65 (σ X0)
             grind)
          | exact superpose b3e65 b3e18
          | exact resolve b3e18 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e78 X0
             have i₂ := b3e65 X0
             grind)
          | exact superpose b3e65 b3e78
          | exact resolve b3e78 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e84 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op X0 X0) = (M.op x X0) ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e16 x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x X0
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e296 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e72
             grind)
          | exact superpose b3e72 b3e15
          | exact resolve b3e15 b3e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e297 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e296
        have b3e298 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e297
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e297
          | exact resolve b3e297 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e297
        have b3e299 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e298
             have i₂ := b3e65 x
             grind)
          | exact superpose b3e65 b3e298
          | exact resolve b3e298 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65 b3e298
        have b3e300 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e299
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e299
          | exact resolve b3e299 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e299
        have b3e687 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e81 y
             grind)
          | exact superpose b3e81 b3e23
          | exact resolve b3e23 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e81
        have b3e3043 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e84 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e3045 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e3043
             have r₂ := b3e20
             grind)
          | exact resolve b3e3043 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3043
        have b3e3050 : (σ (M.op x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e300
             have i₂ := b3e3045
             grind)
          | exact superpose b3e3045 b3e300
          | exact resolve b3e300 b3e3045
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e300 b3e3045
        have b3e3054 : False := by grind
        exact b3e3054
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
          have b4e75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e82 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e75 (σ X0)
               grind)
            | exact superpose b4e75 b4e19
            | exact resolve b4e19 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e82 X0
               have i₂ := b4e75 X0
               grind)
            | exact superpose b4e75 b4e82
            | exact resolve b4e82 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75 b4e82
          have b4e606 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e28
               have i₂ := b4e89 x
               grind)
            | exact superpose b4e89 b4e28
            | (have r₁ := b4e28
               have r₂ := b4e89 x
               grind)
            | exact resolve b4e28 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e89
          have b4e625 : False := by grind
          exact b4e625
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e73 (σ X0)
               grind)
            | exact superpose b5e73 b5e19
            | exact resolve b5e19 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e87 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e80 X0
               have i₂ := b5e73 X0
               grind)
            | exact superpose b5e73 b5e80
            | exact resolve b5e80 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73 b5e80
          have b5e96 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
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
          have b5e100 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e96
          have b5e101 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e100
               have r₂ := b5e25
               grind)
            | exact resolve b5e100 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e100
          have b5e131 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ y) (σ y)
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
          have b5e595 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e87 y
               grind)
            | exact superpose b5e87 b5e23
            | exact resolve b5e23 b5e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87
          have b5e6584 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e131 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131
          have b5e6585 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e6584
               have r₂ := b5e24
               grind)
            | exact resolve b5e6584 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6584
          have b5e6587 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e6585
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e6585
            | exact resolve b5e6585 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6585
          have b5e6589 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e6587
               have i₂ := b5e101
               grind)
            | exact superpose b5e101 b5e6587
            | exact resolve b5e6587 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e101 b5e6587
          have b5e6590 : False := by grind
          exact b5e6590
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e21 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e59 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e64 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e59
        have b6e68 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e64
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e64
          | exact resolve b6e64 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e233 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e68
             grind)
          | exact superpose b6e68 b6e15
          | exact resolve b6e15 b6e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e234 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e233
        have b6e235 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e234
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e234
          | exact resolve b6e234 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e234
        have b6e236 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e235
             have i₂ := b6e63 x
             grind)
          | exact superpose b6e63 b6e235
          | exact resolve b6e235 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63 b6e235
        have b6e240 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e236
             grind)
          | exact superpose b6e236 b6e13
          | exact resolve b6e13 b6e236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e236
        have b6e241 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e240
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e240
          | exact resolve b6e240 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e240
        have b6e334 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e241
             grind)
          | exact superpose b6e241 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e241
        have b6e335 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e334
        have b6e337 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e335
             have r₂ := b6e21
             grind)
          | exact resolve b6e335 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e335
        have b6e339 : False := by grind
        exact b6e339
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e73 (σ X0)
               grind)
            | exact superpose b7e73 b7e19
            | exact resolve b7e19 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e87 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e80 X0
               have i₂ := b7e73 X0
               grind)
            | exact superpose b7e73 b7e80
            | exact resolve b7e80 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73 b7e80
          have b7e98 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ x)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e100 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e98
          have b7e101 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e100
               have r₂ := b7e25
               grind)
            | exact resolve b7e100 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e100
          have b7e102 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e101
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e101
            | exact resolve b7e101 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e103 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e102
               have i₂ := b7e87 y
               grind)
            | exact superpose b7e87 b7e102
            | exact resolve b7e102 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87 b7e102
          have b7e107 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e103
               grind)
            | exact superpose b7e103 b7e14
            | exact resolve b7e14 b7e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103
          have b7e108 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e107
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e107
            | exact resolve b7e107 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e107
          have b7e187 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e108
               grind)
            | exact superpose b7e108 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e188 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e187
          have b7e190 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e188
               have r₂ := b7e21
               grind)
            | exact resolve b7e188 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e188
          have b7e192 : False := by grind
          exact b7e192
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e150 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ y) (σ y)
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
          have b8e6737 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e150 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e150
          have b8e6738 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e6737
               have r₂ := b8e24
               grind)
            | exact resolve b8e6737 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6737
          have b8e6740 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e6738
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e6738
            | exact resolve b8e6738 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6738
          have b8e6745 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e6740
               grind)
            | exact superpose b8e6740 b8e20
            | exact resolve b8e20 b8e6740
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6740
          have b8e6772 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e6745
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e6745
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e6745 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6745
          have b8e6776 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e6772
          have b8e6779 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e6776
               have r₂ := b8e21
               grind)
            | exact resolve b8e6776 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6776
          have b8e6780 : False := by grind
          exact b8e6780

/-- `Equation3499`: `x ◇ x = y ◇ ((z ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation3499 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3499 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3499.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X2) X0)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e31 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op (M.op X1 X1) X0) X2 x
           have i₂ := b0e11 X0 (M.op x x) X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X2
        first
        | (have i₁ := b0e36 X0 x X2
           have i₂ := b0e11 X0 (M.op (M.op x x) X0) x
           grind)
        | (have i₁ := b0e36 X0 x X2
           have i₂ := b0e11 (M.op (M.op x x) X0) x X2
           grind)
        | exact superpose b0e11 b0e36
        | exact resolve b0e36 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e46 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e31 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e31
        | exact resolve b0e31 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e117 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e40 (σ y) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e40
        | exact resolve b0e40 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e157 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e117 (σ x)
           grind)
        | exact superpose b0e117 b0e18
        | exact resolve b0e18 b0e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117
      have b0e162 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e157
           have i₂ := b0e46 x
           grind)
        | exact superpose b0e46 b0e157
        | exact resolve b0e157 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e157
      have b0e163 : False := by grind
      exact b0e163
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
        have b1e110 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
        have b1e116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e110 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e110
        have b1e172 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b1e180 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e172 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e172
          | exact resolve b1e172 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e172
        have b1e457 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e180 (σ y)
             have i₂ := b1e116 (σ y)
             grind)
          | exact superpose b1e116 b1e180
          | (have j1 := b1e116 (σ y)
             grind)
          | exact resolve b1e180 b1e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116 b1e180
        have b1e462 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e457
        have b1e466 : False := by grind
        exact b1e466
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
        have b2e105 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ y) X0
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
        have b2e110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e105 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e105
        have b2e144 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b2e149 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e144 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e144
          | exact resolve b2e144 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e144
        have b2e312 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e149 (σ y)
             have i₂ := b2e110 (σ y)
             grind)
          | exact superpose b2e110 b2e149
          | (have j1 := b2e110 (σ y)
             grind)
          | exact resolve b2e149 b2e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e110 b2e149
        have b2e315 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e312
        have b2e319 : False := by grind
        exact b2e319
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
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
        have b3e33 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e30 X0
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e34 : ∀ X0 : G, (k X0 y) = X0 := by
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
        have b3e96 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e17 X2 X0
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X1
             have j1 := b3e17 X1 X1
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e116 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e96 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e96
        have b3e3841 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e116 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e116
        have b3e3842 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e3841 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3841
        have b3e3843 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e3842 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3842
        have b3e8270 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e34 y
             have i₂ := b3e3843 y
             grind)
          | exact superpose b3e3843 b3e34
          | (have j1 := b3e3843 y
             grind)
          | exact resolve b3e34 b3e3843
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e3843
        have b3e8276 : y = (M.op y y) := by grind
        clear b3e8270
        have b3e8318 : False := by grind
        exact b3e8318
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b4e69 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 x x
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b4e75 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e70 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e76 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have j0 := b4e69 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e389 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e75 (σ X0)
               grind)
            | exact superpose b4e75 b4e19
            | (have j1 := b4e75 (σ X0)
               grind)
            | exact resolve b4e19 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e75454 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e389 y
               grind)
            | exact superpose b4e389 b4e23
            | (have j1 := b4e389 y
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e389 y
               grind)
            | exact resolve b4e23 b4e389
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e389
          have b4e75568 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b4e75454
          have b4e75632 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e75568
               grind)
            | exact superpose b4e75568 b4e20
            | exact resolve b4e20 b4e75568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75568
          have b4e76634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e75632
               have i₂ := b4e76 y
               grind)
            | exact superpose b4e76 b4e75632
            | (have j1 := b4e76 y
               grind)
            | exact resolve b4e75632 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76 b4e75632
          have b4e76649 : y = (M.op y y) := by grind
          clear b4e76634
          have b4e76654 : False := by grind
          exact b4e76654
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
          have b5e81 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
          have b5e87 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e81 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e314 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e34 (σ x)
               have i₂ := b5e87 (σ x)
               grind)
            | exact superpose b5e87 b5e34
            | (have j1 := b5e87 (σ x)
               grind)
            | exact resolve b5e34 b5e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e87
          have b5e317 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e314
          have b5e321 : False := by grind
          exact b5e321
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
        have b6e97 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
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
        have b6e104 : ∀ X0 : G, (M.op y X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e97 X0
             grind)
          | (have r₁ := b6e97 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e97 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e97 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e4146 : y ≠ y ∨ y = (M.op y y) := by
          first
          | (have j0 := b6e104 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e4147 : y = (M.op y y) := by grind
        clear b6e4146
        have b6e4157 : False := by grind
        exact b6e4157
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
          have b7e92 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x x) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 X0
               have i₂ := b7e18 X0 x
               grind)
            | exact superpose b7e18 b7e34
            | (have j1 := b7e18 x x
               grind)
            | exact resolve b7e34 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e101 : ∀ X0 : G, (M.op x X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e92 X0
               grind)
            | (have r₁ := b7e92 x
               have r₂ := b7e22
               grind)
            | (have r₁ := b7e92 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e92 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e4429 : x ≠ x ∨ x = (M.op x x) := by
            first
            | (have j0 := b7e101 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e4430 : x = (M.op x x) := by grind
          clear b7e4429
          have b7e4441 : False := by grind
          exact b7e4441
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X2) X0)) := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e32 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op (M.op X1 X1) X0) X2 x
               have i₂ := b8e13 X0 (M.op x x) X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X2
            first
            | (have i₁ := b8e32 X0 x X2
               have i₂ := b8e13 X0 (M.op (M.op x x) X0) x
               grind)
            | (have i₁ := b8e32 X0 x X2
               have i₂ := b8e13 (M.op (M.op x x) X0) x X2
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e76 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e36 X0 X2
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e36
            | (have j1 := b8e18 X2 X2
               grind)
            | exact resolve b8e36 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e80 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
          have b8e85 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e80 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e196 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e85 (σ X0)
               grind)
            | exact superpose b8e85 b8e19
            | (have j1 := b8e85 (σ X0)
               grind)
            | exact resolve b8e19 b8e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e15799 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e196 x
               grind)
            | exact superpose b8e196 b8e20
            | (have j1 := b8e196 x
               grind)
            | exact resolve b8e20 b8e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e196
          have b8e16004 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e15799
               have r₂ := b8e24
               grind)
            | exact resolve b8e15799 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15799
          have b8e17620 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op X0 y) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e16004
               have i₂ := b8e76 y X0 x
               grind)
            | exact superpose b8e76 b8e16004
            | (have j1 := b8e76 y X0 x
               grind)
            | exact resolve b8e16004 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76 b8e16004
          have b8e17627 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have j0 := b8e17620 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17620
          have b8e17634 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e17627 X0
               grind)
            | (have r₁ := b8e17627 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e17627 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17627
          have b8e18180 : y ≠ y := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e17634 y
               grind)
            | exact superpose b8e17634 b8e21
            | (have r₁ := b8e21
               have r₂ := b8e17634 y
               grind)
            | exact resolve b8e21 b8e17634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17634
          have b8e18181 : False := by grind
          exact b8e18181

/-- `Equation3515`: `x ◇ y = x ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pxy_Equation3515 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3515 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3515.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e75 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e79 : False := by grind
      exact b0e79
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
          have b4e60 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e32 x
               grind)
            | exact superpose b4e32 b4e27
            | (have r₁ := b4e27
               have r₂ := b4e32 x
               grind)
            | exact resolve b4e27 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e32
          have b4e62 : False := by grind
          exact b4e62
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X2) X1)) := by
            intro X0 X1 X2
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
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20
            | exact resolve b5e20 b5e22
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
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e50 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e59 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ x = (k x y) := by
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
          have b5e61 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ X0) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X0) X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e17
            | (have j0 := b5e17 (σ X0) X1
               grind)
            | exact resolve b5e17 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : x = y ∨ x = (k x y) := by grind
          clear b5e59
          have b5e64 : x = (k x y) := by
            first
            | (have r₁ := b5e63
               have r₂ := b5e21
               grind)
            | exact resolve b5e63 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e67 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ X0 = X2 ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e18 X0 X1
               have i₂ := b5e18 X0 X2
               grind)
            | (have i₁ := b5e18 X1 X1
               have i₂ := b5e18 X1 X1
               grind)
            | exact superpose b5e18 b5e18
            | (have j0 := b5e18 X0 X2
               have j1 := b5e18 X0 X2
               grind)
            | exact resolve b5e18 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e79 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e31 X0
               have i₂ := b5e18 (σ X0) X1
               grind)
            | (have i₁ := b5e31 X0
               have i₂ := b5e18 (σ X0) (σ X0)
               grind)
            | exact superpose b5e18 b5e31
            | (have j1 := b5e18 (σ X0) X1
               grind)
            | exact resolve b5e31 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e70 X0 X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e70
            | (have j0 := b5e70 X0 X1
               grind)
            | exact resolve b5e70 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70
          have b5e308 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e84 x y
               grind)
            | exact superpose b5e84 b5e24
            | (have j1 := b5e84 x y
               grind)
            | exact resolve b5e24 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e310 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ X0) (M.op (σ (k X0 X1)) X2)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X0) X2 (σ X1)
               have i₂ := b5e84 X0 X1
               grind)
            | exact superpose b5e84 b5e13
            | (have j1 := b5e84 X0 X1
               grind)
            | exact resolve b5e13 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e362 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e308
               have r₂ := b5e26
               grind)
            | exact resolve b5e308 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e308
          have b5e384 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b5e362
               have r₂ := b5e23
               grind)
            | exact resolve b5e362 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e362
          have b5e395 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e384
               have i₂ := b5e64
               grind)
            | exact superpose b5e64 b5e384
            | exact resolve b5e384 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e384
          have b5e401 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e395
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e395
            | exact resolve b5e395 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e395
          have b5e484 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e26
               have i₂ := b5e67 (σ x) (σ y) X0
               grind)
            | (have i₁ := b5e26
               have i₂ := b5e67 (σ x) X0 (σ y)
               grind)
            | exact superpose b5e67 b5e26
            | (have j1 := b5e67 (σ x) (σ y) (σ y)
               grind)
            | (have r₁ := b5e26
               have r₂ := b5e67 (M.op (σ x) (σ y)) x (σ (M.op x x))
               grind)
            | (have r₁ := b5e26
               have r₂ := b5e67 (σ (M.op x x)) x (M.op (σ x) (σ y))
               grind)
            | (have r₁ := b5e26
               have r₂ := b5e67 (M.op (σ x) (σ y)) (σ (M.op x x)) x
               grind)
            | exact resolve b5e26 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67
          have b5e515 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have j0 := b5e484 X0
               grind)
            | (have r₁ := b5e484 X0
               have r₂ := b5e23
               grind)
            | (have r₁ := b5e484 (σ y)
               have r₂ := b5e23
               grind)
            | exact resolve b5e484 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e484
          have b5e531 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have j0 := b5e515 X0
               have j1 := b5e79 x X0
               grind)
            | (have r₁ := b5e515 x
               have r₂ := b5e79 x x
               grind)
            | (have r₁ := b5e515 X0
               have r₂ := b5e79 (M.op x x) (M.op (σ x) X0)
               grind)
            | exact resolve b5e515 b5e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79 b5e515
          have b5e539 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e531 X0
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e531
            | (have j0 := b5e531 X0
               grind)
            | exact resolve b5e531 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e531
          have b5e547 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e539 X0
               have i₂ := b5e64
               grind)
            | exact superpose b5e64 b5e539
            | (have j0 := b5e539 X0
               grind)
            | exact resolve b5e539 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e539
          have b5e4582 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e310 x y X0
               have i₂ := b5e64
               grind)
            | exact superpose b5e64 b5e310
            | (have j0 := b5e310 x y x
               grind)
            | exact resolve b5e310 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e310
          have b5e4650 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e4582 X0
               grind)
            | (have r₁ := b5e4582 X0
               have r₂ := b5e26
               grind)
            | exact resolve b5e4582 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e4582
          have b5e4667 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have j0 := b5e4650 X0
               grind)
            | (have r₁ := b5e4650 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e4650 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4650
          have b5e4680 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e4667 (σ y)
               have i₂ := b5e547 X0
               grind)
            | exact superpose b5e547 b5e4667
            | (have j1 := b5e547 X0
               grind)
            | exact resolve b5e4667 b5e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e547
          have b5e4682 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b5e4667 (σ x)
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e4667
            | exact resolve b5e4667 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4667
          have b5e4731 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e4680 X0
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e4680
            | (have j0 := b5e4680 X0
               grind)
            | exact resolve b5e4680 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e4680
          have b5e4732 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have j0 := b5e4731 X0
               grind)
            | (have r₁ := b5e4731 X0
               have r₂ := b5e401
               grind)
            | (have r₁ := b5e4731 (σ (M.op x x))
               have r₂ := b5e401
               grind)
            | exact resolve b5e4731 b5e401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4731
          have b5e4825 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b5e61 x (σ (M.op x x))
               have i₂ := b5e4682
               grind)
            | exact superpose b5e4682 b5e61
            | (have j0 := b5e61 x (σ (M.op x x))
               grind)
            | (have r₁ := b5e61 x (σ (M.op x x))
               have r₂ := b5e4682
               grind)
            | exact resolve b5e61 b5e4682
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e4844 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ (M.op x x))) := by grind
          clear b5e4825
          have b5e4849 : (σ x) = (k (σ x) (σ (M.op x x))) := by
            first
            | (have r₁ := b5e4844
               have r₂ := b5e401
               grind)
            | exact resolve b5e4844 b5e401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4844
          have b5e4854 : (σ x) = (σ (k x (M.op x x))) := by
            first
            | (have i₁ := b5e4849
               have i₂ := b5e19 x (M.op x x)
               grind)
            | exact superpose b5e19 b5e4849
            | exact resolve b5e4849 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4849
          have b5e5237 : (τ (σ x)) = (k x (M.op x x)) := by
            first
            | (have i₁ := b5e14 (k x (M.op x x))
               have i₂ := b5e4854
               grind)
            | exact superpose b5e4854 b5e14
            | exact resolve b5e14 b5e4854
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4854
          have b5e5293 : x = (k x (M.op x x)) := by
            first
            | (have i₁ := b5e5237
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e5237
            | exact resolve b5e5237 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5237
          have b5e5875 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e50 x X0
               have i₂ := b5e4732 X0
               grind)
            | exact superpose b5e4732 b5e50
            | (have j1 := b5e4732 X0
               grind)
            | exact resolve b5e50 b5e4732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e4732
          have b5e8308 : (τ (σ (M.op x x))) = (k x (τ (σ (M.op x x)))) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e5875 (σ (M.op x x))
               have i₂ := b5e4682
               grind)
            | exact superpose b5e4682 b5e5875
            | (have j0 := b5e5875 (σ (M.op x x))
               grind)
            | exact resolve b5e5875 b5e4682
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4682 b5e5875
          have b5e8384 : (τ (σ (M.op x x))) = (k x (τ (σ (M.op x x)))) := by
            first
            | (have r₁ := b5e8308
               have r₂ := b5e401
               grind)
            | exact resolve b5e8308 b5e401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8308
          have b5e8389 : (M.op x x) = (k x (M.op x x)) := by
            first
            | (have i₁ := b5e8384
               have i₂ := b5e14 (M.op x x)
               grind)
            | exact superpose b5e14 b5e8384
            | exact resolve b5e8384 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8384
          have b5e8392 : x = (M.op x x) := by
            first
            | (have i₁ := b5e8389
               have i₂ := b5e5293
               grind)
            | exact superpose b5e5293 b5e8389
            | exact resolve b5e8389 b5e5293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5293 b5e8389
          have b5e8469 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e401
               have i₂ := b5e8392
               grind)
            | exact superpose b5e8392 b5e401
            | exact resolve b5e401 b5e8392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e401 b5e8392
          have b5e8521 : False := by grind
          exact b5e8521
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X2) X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e61 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e64 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e61
          have b7e65 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e23
               grind)
            | exact resolve b7e64 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e66 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e65
            | exact resolve b7e65 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e70 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e14
            | exact resolve b7e14 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e71 : x = (k x y) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e70
            | exact resolve b7e70 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e99 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e100 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e99
               have r₂ := b7e22
               grind)
            | exact resolve b7e99 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e102 : x = (M.op x y) := by
            first
            | (have r₁ := b7e100
               have r₂ := b7e21
               grind)
            | exact resolve b7e100 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100
          have b7e128 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e22
            | exact resolve b7e22 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e131 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 x X0 y
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e13
            | exact resolve b7e13 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e242 : x = (M.op x x) := by
            first
            | (have i₁ := b7e131 y
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e131
            | exact resolve b7e131 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102 b7e131
          have b7e254 : False := by grind
          exact b7e254
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e77 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e77
            | (have j0 := b8e77 X0 X1
               grind)
            | exact resolve b8e77 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e338 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e90 x y
               grind)
            | exact superpose b8e90 b8e20
            | (have j1 := b8e90 x y
               grind)
            | exact resolve b8e20 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e396 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e338
               have r₂ := b8e23
               grind)
            | exact resolve b8e338 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e338
          have b8e1282 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e396
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e396
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e396
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e396
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e396 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e396
          have b8e1283 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
          clear b8e1282
          have b8e1287 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have r₁ := b8e1283
               have r₂ := b8e22
               grind)
            | exact resolve b8e1283 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1283
          have b8e1291 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e1287
               have r₂ := b8e21
               grind)
            | exact resolve b8e1287 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1287
          have b8e1295 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e1291
               grind)
            | exact superpose b8e1291 b8e24
            | exact resolve b8e24 b8e1291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1291
          have b8e1315 : False := by grind
          exact b8e1315
