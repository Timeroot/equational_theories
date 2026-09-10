import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4480`: `x ◇ (y ◇ y) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pxy_Equation4480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4480.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X0) X1) := by
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
      have b0e29 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e11 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e11 (σ y) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
      have b0e34 : (M.op y x) = (k x y) := by grind
      have b0e35 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e33
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e33
        | exact resolve b0e33 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e36 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b0e35
           have i₂ := b0e34
           grind)
        | exact superpose b0e34 b0e35
        | exact resolve b0e35 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e35
      have b0e94 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e30
           grind)
        | exact superpose b0e30 b0e18
        | exact resolve b0e18 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e97 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e94
           have i₂ := b0e36
           grind)
        | exact superpose b0e36 b0e94
        | exact resolve b0e94 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e94
      have b0e98 : (σ (M.op y x)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e97
           have i₂ := b0e29
           grind)
        | exact superpose b0e29 b0e97
        | exact resolve b0e97 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29 b0e97
      have b0e99 : False := by grind
      exact b0e99
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X0) X1) := by
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
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b1e27 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e12 y y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e32 : (M.op y x) = (k x y) := by grind
        have b1e33 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e31
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e31
          | exact resolve b1e31 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e34 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        have b1e37 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b1e38 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e37 X0
             have i₂ := b1e12 X0 X0
             grind)
          | exact superpose b1e12 b1e37
          | (have j0 := b1e37 X0
             grind)
          | exact resolve b1e37 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e39 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e34
             have r₂ := b1e21
             grind)
          | exact resolve b1e34 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e40 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e39
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e39
          | exact resolve b1e39 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e41 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e32
             grind)
          | exact superpose b1e32 b1e40
          | exact resolve b1e40 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e40
        have b1e44 : (M.op y x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e13
          | exact resolve b1e13 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : x = (M.op y x) := by
          first
          | (have i₁ := b1e44
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e44
          | exact resolve b1e44 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b1e74 : (M.op x y) = (M.op x (M.op y y)) := by
          first
          | (have i₁ := b1e12 x y
             have i₂ := b1e45
             grind)
          | exact superpose b1e45 b1e12
          | exact resolve b1e12 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e75 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b1e74
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e74
          | exact resolve b1e74 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e76 : (M.op y x) = (M.op x x) := by
          first
          | (have i₁ := b1e75
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e75
          | exact resolve b1e75 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e77 : x = (M.op x x) := by
          first
          | (have i₁ := b1e76
             have i₂ := b1e45
             grind)
          | exact superpose b1e45 b1e76
          | exact resolve b1e76 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e84 : (M.op x x) = (k x x) := by grind
        have b1e85 : x = (k x x) := by
          first
          | (have i₁ := b1e84
             have i₂ := b1e77
             grind)
          | exact superpose b1e77 b1e84
          | exact resolve b1e84 b1e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77 b1e84
        have b1e100 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e33
             grind)
          | exact superpose b1e33 b1e19
          | exact resolve b1e19 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e103 : (σ (k y x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e100
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e100
          | exact resolve b1e100 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e100
        have b1e104 : (σ x) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e103
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e103
          | exact resolve b1e103 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e103
        have b1e233 : (M.op y x) = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e38 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e38
          | exact resolve b1e38 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e241 : x = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e233
             have i₂ := b1e45
             grind)
          | exact superpose b1e45 b1e233
          | exact resolve b1e233 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45 b1e233
        have b1e254 : (σ x) ≠ (σ x) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e104
             have i₂ := b1e241
             grind)
          | exact superpose b1e241 b1e104
          | exact resolve b1e104 b1e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e241
        have b1e258 : y = (k y x) := by grind
        clear b1e254
        have b1e315 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e104
             have i₂ := b1e258
             grind)
          | exact superpose b1e258 b1e104
          | exact resolve b1e104 b1e258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104 b1e258
        have b1e847 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e70 x x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e70
          | exact resolve b1e70 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e1027 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b1e847
        have b1e1044 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b1e1027
             have r₂ := b1e315
             grind)
          | exact resolve b1e1027 b1e315
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1027
        have b1e1055 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e1044
             have i₂ := b1e85
             grind)
          | exact superpose b1e85 b1e1044
          | exact resolve b1e1044 b1e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e85 b1e1044
        have b1e1057 : False := by grind
        exact b1e1057
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X0) X1) := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b2e12 y y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : (M.op y x) = (k x y) := by grind
        have b2e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
             have r₂ := b2e17 (σ y) (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e570 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e58 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e571 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e570
             have r₂ := b2e21
             grind)
          | exact resolve b2e570 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e570
        have b2e572 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e571
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e571
          | exact resolve b2e571 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e571
        have b2e573 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b2e572
             have i₂ := b2e30
             grind)
          | exact superpose b2e30 b2e572
          | exact resolve b2e572 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e572
        have b2e574 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e573
             grind)
          | exact superpose b2e573 b2e19
          | exact resolve b2e19 b2e573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e573
        have b2e580 : (σ (M.op y x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b2e574
             have i₂ := b2e27
             grind)
          | exact superpose b2e27 b2e574
          | exact resolve b2e574 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e574
        have b2e581 : False := by grind
        exact b2e581
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X0) X1) := by
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
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b3e27 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b3e12 x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e28 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e12 (σ y) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : (M.op y (M.op x x)) = (M.op (M.op y x) x) := by
          first
          | (have i₁ := b3e12 y x
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e12
          | exact resolve b3e12 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : (M.op y y) = (M.op (M.op y x) x) := by
          first
          | (have i₁ := b3e30
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e30
          | exact resolve b3e30 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e32 : (M.op x y) = (k y x) := by grind
        have b3e33 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b3e34 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
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
        have b3e35 : (M.op y x) = (k y x) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e32
          | exact resolve b3e32 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e36 : x = (M.op y y) ∨ x = (k x y) := by grind
        have b3e37 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        have b3e41 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
        have b3e42 : x = (k x y) := by
          first
          | (have r₁ := b3e36
             have r₂ := b3e20
             grind)
          | exact resolve b3e36 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e43 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e41
             have i₂ := b3e35
             grind)
          | exact superpose b3e35 b3e41
          | exact resolve b3e41 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e84 : (M.op (σ x) (M.op (σ y) (σ y))) = (M.op (σ (k x y)) (σ y)) := by
          first
          | (have i₁ := b3e12 (σ x) (σ y)
             have i₂ := b3e34
             grind)
          | exact superpose b3e34 b3e12
          | exact resolve b3e12 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e85 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b3e84
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e84
          | exact resolve b3e84 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e86 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e85
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e85
          | exact resolve b3e85 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e87 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e86
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e86
          | exact resolve b3e86 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86
        have b3e88 : (σ (k x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e87
             have i₂ := b3e34
             grind)
          | exact superpose b3e34 b3e87
          | exact resolve b3e87 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87
        have b3e89 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e88
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e88
          | exact resolve b3e88 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88
        have b3e95 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        have b3e96 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e95
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e95
          | exact resolve b3e95 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e95
        have b3e97 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e96
             have i₂ := b3e89
             grind)
          | exact superpose b3e89 b3e96
          | exact resolve b3e96 b3e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89 b3e96
        have b3e98 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e19
          | exact resolve b3e19 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e101 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e98
             have i₂ := b3e34
             grind)
          | exact superpose b3e34 b3e98
          | exact resolve b3e98 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98
        have b3e103 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e101
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e101
          | exact resolve b3e101 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e101
        have b3e105 : (σ x) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b3e103
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e103
          | exact resolve b3e103 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e103
        have b3e114 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op y x)) := by grind
        clear b3e43
        have b3e115 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e114
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e114
          | exact resolve b3e114 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e114
        have b3e116 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e115
             have i₂ := b3e35
             grind)
          | exact superpose b3e35 b3e115
          | exact resolve b3e115 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35 b3e115
        have b3e117 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e116
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e116
          | exact resolve b3e116 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e116
        have b3e118 : (σ (k x y)) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e117
             have i₂ := b3e34
             grind)
          | exact superpose b3e34 b3e117
          | exact resolve b3e117 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e117
        have b3e119 : (σ x) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e118
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e118
          | exact resolve b3e118 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42 b3e118
        have b3e120 : (σ y) = (σ (M.op y x)) := by
          first
          | (have r₁ := b3e119
             have r₂ := b3e105
             grind)
          | exact resolve b3e119 b3e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e119
        have b3e121 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e105
             have i₂ := b3e120
             grind)
          | exact superpose b3e120 b3e105
          | exact resolve b3e105 b3e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e105
        have b3e124 : (M.op y x) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (M.op y x)
             have i₂ := b3e120
             grind)
          | exact superpose b3e120 b3e13
          | exact resolve b3e13 b3e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e120
        have b3e125 : y = (M.op y x) := by
          first
          | (have i₁ := b3e124
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e124
          | exact resolve b3e124 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e124
        have b3e196 : (M.op y y) = (M.op y x) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e125
             grind)
          | exact superpose b3e125 b3e31
          | exact resolve b3e31 b3e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e198 : y = (M.op y y) := by
          first
          | (have i₁ := b3e196
             have i₂ := b3e125
             grind)
          | exact superpose b3e125 b3e196
          | exact resolve b3e196 b3e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e125 b3e196
        have b3e224 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e198
             grind)
          | exact superpose b3e198 b3e20
          | exact resolve b3e20 b3e198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e198
        have b3e432 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e97
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e97
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e97 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e97
        have b3e438 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b3e432
        have b3e444 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e438
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e438
          | exact resolve b3e438 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e438
        have b3e445 : x = (M.op x x) := by
          first
          | (have r₁ := b3e444
             have r₂ := b3e121
             grind)
          | exact resolve b3e444 b3e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e121 b3e444
        have b3e446 : x = y := by
          first
          | (have i₁ := b3e445
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e445
          | exact resolve b3e445 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e445
        have b3e447 : False := by grind
        exact b3e447
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
          have b4e37 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e38 : (M.op x y) = (k y x) := by grind
          have b4e39 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e37
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e37
            | exact resolve b4e37 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e40 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e39
               have i₂ := b4e38
               grind)
            | exact superpose b4e38 b4e39
            | exact resolve b4e39 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e39
          have b4e41 : False := by grind
          exact b4e41
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X0) X1) := by
            intro X0 X1
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e13 X0 X1
               have i₂ := b5e18 (M.op X1 X0) X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X1
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e333 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e339 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e333 X0 X1
               have j1 := b5e51 X0 X1
               grind)
            | (have r₁ := b5e333 X0 X0
               have r₂ := b5e51 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b5e333 X0 X1
               have r₂ := b5e51 X0 X1
               grind)
            | (have r₁ := b5e333 X1 X0
               have r₂ := b5e51 X0 X1
               grind)
            | exact resolve b5e333 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e333
          have b5e362 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          clear b5e339
          have b5e1300 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e362 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e362
          have b5e1301 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e1300 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1300
          have b5e1500 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e1301 (σ X0)
               grind)
            | exact superpose b5e1301 b5e19
            | exact resolve b5e19 b5e1301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1507 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e1500 X0
               have i₂ := b5e1301 X0
               grind)
            | exact superpose b5e1301 b5e1500
            | exact resolve b5e1500 b5e1301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1301 b5e1500
          have b5e1950 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1507 x
               grind)
            | exact superpose b5e1507 b5e24
            | exact resolve b5e24 b5e1507
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1507
          have b5e1995 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e1950
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1950
            | exact resolve b5e1950 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1950
          have b5e1996 : False := by grind
          exact b5e1996
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X0) X1) := by
          intro X0 X1
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b6e27 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e12 (σ y) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e33 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b6e34 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e33
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e33
          | exact resolve b6e33 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e85 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e27
             grind)
          | exact superpose b6e27 b6e19
          | exact resolve b6e19 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e88 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e85
             have i₂ := b6e34
             grind)
          | exact superpose b6e34 b6e85
          | exact resolve b6e85 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34 b6e85
        have b6e89 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e88
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e88
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e88 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e90 : x = (M.op y y) ∨ y = (M.op x x) := by grind
        clear b6e89
        have b6e91 : y = (M.op x x) := by
          first
          | (have r₁ := b6e90
             have r₂ := b6e20
             grind)
          | exact resolve b6e90 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e92 : False := by grind
        exact b6e92
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X0) X1) := by
            intro X0 X1
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e43 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b7e45 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e43
            | exact resolve b7e43 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e46 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e20
            | exact resolve b7e20 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          have b7e51 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            grind
          have b7e52 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e51 X0
               have i₂ := b7e13 X0 X0
               grind)
            | exact superpose b7e13 b7e51
            | (have j0 := b7e51 X0
               grind)
            | exact resolve b7e51 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e53 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e49
               have r₂ := b7e23
               grind)
            | exact resolve b7e49 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
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
          have b7e70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X1
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e13 X0 X1
               have i₂ := b7e18 (M.op X1 X0) X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X0 X1
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e72 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b7e85 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
          have b7e88 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e85
               have r₂ := b7e21
               grind)
            | exact resolve b7e85 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e89 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e88
               have r₂ := b7e22
               grind)
            | exact resolve b7e88 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e166 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e46
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e46 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e167 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e166
               have r₂ := b7e22
               grind)
            | exact resolve b7e166 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e166
          have b7e170 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b7e167
               have r₂ := b7e21
               grind)
            | exact resolve b7e167 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e167
          have b7e173 : (σ x) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b7e170
               have i₂ := b7e89
               grind)
            | exact superpose b7e89 b7e170
            | exact resolve b7e170 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e170
          have b7e326 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e332 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e326 X0 X1
               have j1 := b7e70 X0 X1
               grind)
            | (have r₁ := b7e326 X0 X0
               have r₂ := b7e70 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b7e326 X0 X1
               have r₂ := b7e70 X0 X1
               grind)
            | (have r₁ := b7e326 X1 X0
               have r₂ := b7e70 X0 X1
               grind)
            | exact resolve b7e326 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e326
          have b7e449 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e52 X0
               have i₂ := b7e332 X0 X1
               grind)
            | (have i₁ := b7e52 X0
               have i₂ := b7e332 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e332 b7e52
            | (have j1 := b7e332 X1 X0
               grind)
            | exact resolve b7e52 b7e332
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52 b7e332
          have b7e469 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e449 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e449
          have b7e729 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e83 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e83
            | exact resolve b7e83 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e911 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e729
          have b7e948 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e911
               grind)
            | exact superpose b7e911 b7e14
            | exact resolve b7e14 b7e911
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e911
          have b7e962 : y = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e948
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e948
            | exact resolve b7e948 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e948
          have b7e1127 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e469 x x
               have i₂ := b7e962
               grind)
            | exact superpose b7e962 b7e469
            | exact resolve b7e469 b7e962
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e469 b7e962
          have b7e1134 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b7e1127
               have r₂ := b7e22
               grind)
            | exact resolve b7e1127 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1127
          have b7e1311 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e1134
               grind)
            | exact superpose b7e1134 b7e14
            | exact resolve b7e14 b7e1134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1134
          have b7e1329 : x = y ∨ x = y := by
            first
            | (have i₁ := b7e1311
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1311
            | exact resolve b7e1311 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1311
          have b7e1330 : x = y := by grind
          clear b7e1329
          have b7e1504 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e89
               have i₂ := b7e1330
               grind)
            | exact superpose b7e1330 b7e89
            | exact resolve b7e89 b7e1330
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e1508 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e173
               have i₂ := b7e1330
               grind)
            | exact superpose b7e1330 b7e173
            | exact resolve b7e173 b7e1330
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e173 b7e1330
          have b7e1511 : False := by grind
          exact b7e1511
        · have b8e13 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X0) X1) := by
            intro X0 X1
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e13 X0 X1
               have i₂ := b8e18 (M.op X1 X0) X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e452 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e76 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e459 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e452 X0 X1
               have j1 := b8e74 X0 X1
               grind)
            | (have r₁ := b8e452 X0 X0
               have r₂ := b8e74 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b8e452 X0 X1
               have r₂ := b8e74 X0 X1
               grind)
            | (have r₁ := b8e452 X1 X0
               have r₂ := b8e74 X0 X1
               grind)
            | exact resolve b8e452 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74 b8e452
          have b8e501 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e459 (σ x) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e459 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e459 b8e24
            | (have j1 := b8e459 (σ x) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e459 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e459
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e748 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e501 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e501
          have b8e749 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e748
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e748
            | exact resolve b8e748 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e748
          have b8e753 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e749
               grind)
            | exact superpose b8e749 b8e20
            | exact resolve b8e20 b8e749
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e749
          have b8e966 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e753
               have i₂ := b8e459 x y
               grind)
            | exact superpose b8e459 b8e753
            | (have j1 := b8e459 x y
               grind)
            | exact resolve b8e753 b8e459
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e459 b8e753
          have b8e969 : y = (M.op x x) := by grind
          clear b8e966
          have b8e975 : False := by grind
          exact b8e975

/-- `Equation4486`: `x ◇ (y ◇ y) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pyx_pxy_Equation4486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4486.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e36 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ y) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e37 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e37
        | exact resolve b0e37 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e42 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e36 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e36
        | exact resolve b0e36 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e97 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e42 (σ x)
           grind)
        | exact superpose b0e42 b0e18
        | exact resolve b0e18 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e100 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e97
           have i₂ := b0e41 x
           grind)
        | exact superpose b0e41 b0e97
        | exact resolve b0e97 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e97
      have b0e101 : False := by grind
      exact b0e101
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b1e90 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
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
        have b1e96 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b1e90 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e90
        have b1e160 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b1e168 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e160 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e160
          | exact resolve b1e160 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e160
        have b1e733 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e168 (σ y)
             have i₂ := b1e96 (σ y)
             grind)
          | exact superpose b1e96 b1e168
          | (have j1 := b1e96 (σ y)
             grind)
          | exact resolve b1e168 b1e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e96 b1e168
        have b1e738 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e733
        have b1e743 : False := by grind
        exact b1e743
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b2e73 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
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
        have b2e79 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b2e73 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e113 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b2e118 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e113 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e113
          | exact resolve b2e113 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e113
        have b2e667 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e118 (σ y)
             have i₂ := b2e79 (σ y)
             grind)
          | exact superpose b2e79 b2e118
          | (have j1 := b2e79 (σ y)
             grind)
          | exact resolve b2e118 b2e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79 b2e118
        have b2e670 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e667
        have b2e675 : False := by grind
        exact b2e675
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e44 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
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
        have b3e50 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e44 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e44
          | exact resolve b3e44 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e61 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e16 (σ y) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 (σ y) X0
             grind)
          | (have r₁ := b3e16 (σ y) x
             have r₂ := b3e22
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e64 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
          intro X0
          first
          | (have j0 := b3e61 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e67 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e64 X0
             have i₂ := b3e50 X0
             grind)
          | exact superpose b3e50 b3e64
          | (have j0 := b3e64 X0
             grind)
          | exact resolve b3e64 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e64
        have b3e71 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
          intro X0
          first
          | (have j0 := b3e67 X0
             have j1 := b3e15 (σ y) X0
             grind)
          | (have r₁ := b3e67 x
             have r₂ := b3e15 X0 x
             grind)
          | exact resolve b3e67 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e79 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
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
        have b3e97 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e79 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e120 : ∀ X0 : G, (σ y) = (σ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 y X0
             have i₂ := b3e71 (σ X0)
             grind)
          | exact superpose b3e71 b3e18
          | exact resolve b3e18 b3e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e186 : ∀ X0 : G, (k y X0) = (τ (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e13 (k y X0)
             have i₂ := b3e120 X0
             grind)
          | exact superpose b3e120 b3e13
          | exact resolve b3e13 b3e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e120
        have b3e187 : ∀ X0 : G, y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e186 X0
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e186
          | exact resolve b3e186 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e186
        have b3e5405 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e97 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e97
        have b3e5406 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e5405 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5405
        have b3e5407 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e5406 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5406
        have b3e6983 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e187 y
             have i₂ := b3e5407 y
             grind)
          | exact superpose b3e5407 b3e187
          | (have j1 := b3e5407 y
             grind)
          | exact resolve b3e187 b3e5407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e187 b3e5407
        have b3e6985 : y = (M.op y y) := by grind
        clear b3e6983
        have b3e7035 : False := by grind
        exact b3e7035
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b4e40 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (σ x)) := by
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
          have b4e41 : ∀ X0 : G, (M.op x x) = (M.op X0 x) := by
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
          have b4e42 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e13 X2 X1 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e41 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e41
            | exact resolve b4e41 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e46 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e40 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e40
            | exact resolve b4e40 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e50 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e45 X1
               grind)
            | exact superpose b4e45 b4e13
            | exact resolve b4e13 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e75 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X2 X0
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e81 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X2
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e83 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X0 X2
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e18 X2 X2
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e86 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e23
               have i₂ := b4e18 (σ y) X0
               grind)
            | exact superpose b4e18 b4e23
            | (have j1 := b4e18 X0 X0
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e18 X0 (σ y)
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e18 (σ y) x
               grind)
            | exact resolve b4e23 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e18 (σ X0) (σ X1)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X1) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e91 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b4e86 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e86
          have b4e92 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e83 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83
          have b4e93 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e81 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81
          have b4e96 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e75 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e103 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (σ x)
               have i₂ := b4e46 X1
               grind)
            | exact superpose b4e46 b4e13
            | exact resolve b4e13 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e108 : ∀ X1 : G, (M.op (σ x) X1) = (M.op x X1) := by
            intro X1
            first
            | (have i₁ := b4e103 x X1
               have i₂ := b4e50 x X1
               grind)
            | exact superpose b4e50 b4e103
            | exact resolve b4e103 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103
          have b4e122 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e108 (σ y)
               grind)
            | exact superpose b4e108 b4e20
            | exact resolve b4e20 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e108
          have b4e178 : ∀ X0 X2 : G, (M.op x X0) = (M.op (M.op X0 X2) X0) := by
            intro X0 X2
            first
            | (have i₁ := b4e13 x X0 X2
               have i₂ := b4e50 x X0
               grind)
            | exact superpose b4e50 b4e13
            | exact resolve b4e13 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e182 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x X0)) = (M.op (M.op (M.op X0 X0) X2) (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op X0 X0) X2
               have i₂ := b4e50 (M.op X0 X0) X0
               grind)
            | exact superpose b4e50 b4e13
            | exact resolve b4e13 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e190 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e182 X0 X1 x
               have i₂ := b4e50 (M.op (M.op X0 X0) x) X0
               grind)
            | exact superpose b4e50 b4e182
            | exact resolve b4e182 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e182
          have b4e927 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e42 X0 X0 X2
               have i₂ := b4e91 X0
               grind)
            | exact superpose b4e91 b4e42
            | (have j1 := b4e91 X0
               grind)
            | exact resolve b4e42 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e5463 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e93 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93
          have b4e5468 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e5463 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5463
          have b4e5873 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e96 X1 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96
          have b4e5877 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e5873 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5873
          have b4e6575 : ∀ X0 X1 : G, (M.op x (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e50 X1 (σ X0)
               have i₂ := b4e87 X0 X0
               grind)
            | exact superpose b4e87 b4e50
            | (have j1 := b4e87 X0 X0
               grind)
            | exact resolve b4e50 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87
          have b4e6700 : ∀ X0 X1 : G, (M.op x (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e6575 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6575
          have b4e9346 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e23
               have i₂ := b4e927 (σ y) (σ y) X0
               grind)
            | (have i₁ := b4e23
               have i₂ := b4e927 (σ y) X0 (σ y)
               grind)
            | exact superpose b4e927 b4e23
            | (have j1 := b4e927 (σ y) x x
               grind)
            | exact resolve b4e23 b4e927
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e9391 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op (σ y) X1) = (k (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e91 X1
               have i₂ := b4e927 X1 X1 X0
               grind)
            | (have i₁ := b4e91 X1
               have i₂ := b4e927 X1 X0 X1
               grind)
            | exact superpose b4e927 b4e91
            | (have j0 := b4e91 X1
               have j1 := b4e927 X1 X1 x
               grind)
            | exact resolve b4e91 b4e927
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91 b4e927
          have b4e9523 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e9391 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9391
          have b4e9572 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have j1 := b4e9523 x (σ y)
               grind)
            | (have r₁ := b4e9346 x
               have r₂ := b4e9523 x (σ y)
               grind)
            | exact resolve b4e9346 b4e9523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9346 b4e9523
          have b4e9624 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e9572
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e9572
            | exact resolve b4e9572 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9572
          have b4e9699 : (M.op x (σ y)) = (M.op (σ (k y y)) (σ y)) := by
            first
            | (have i₁ := b4e178 (σ y) (σ y)
               have i₂ := b4e9624
               grind)
            | exact superpose b4e9624 b4e178
            | exact resolve b4e178 b4e9624
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9624
          have b4e24769 : (M.op x (σ y)) ≠ (M.op (σ y) (σ (k y y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x (σ y)) = (k (σ (k y y)) (σ y)) := by
            first
            | (have i₁ := b4e5468 (σ (k y y)) (σ y)
               have i₂ := b4e9699
               grind)
            | exact superpose b4e9699 b4e5468
            | (have j0 := b4e5468 x (σ y)
               grind)
            | exact resolve b4e5468 b4e9699
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5468 b4e9699
          have b4e24771 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x (σ y)) = (k (σ (k y y)) (σ y)) := by
            first
            | (have j1 := b4e6700 y x
               grind)
            | (have r₁ := b4e24769
               have r₂ := b4e6700 y (σ y)
               grind)
            | exact resolve b4e24769 b4e6700
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6700 b4e24769
          have b4e24795 : (M.op x (σ y)) = (k (σ (k y y)) (σ y)) := by
            first
            | (have r₁ := b4e24771
               have r₂ := b4e23
               grind)
            | exact resolve b4e24771 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24771
          have b4e24805 : (M.op x (σ y)) = (σ (k (k y y) y)) := by
            first
            | (have i₁ := b4e24795
               have i₂ := b4e19 (k y y) y
               grind)
            | exact superpose b4e19 b4e24795
            | exact resolve b4e24795 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24795
          have b4e25492 : (M.op x (σ y)) = (σ (k (M.op y y) y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e24805
               have i₂ := b4e18 y y
               grind)
            | exact superpose b4e18 b4e24805
            | (have j1 := b4e18 y y
               grind)
            | exact resolve b4e24805 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24805
          have b4e25560 : (M.op x (σ y)) = (σ (k (M.op y y) y)) ∨ y = (M.op y y) := by grind
          clear b4e25492
          have b4e25588 : (M.op x (σ y)) = (σ (k (M.op y y) y)) := by
            first
            | (have r₁ := b4e25560
               have r₂ := b4e21
               grind)
            | exact resolve b4e25560 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25560
          have b4e30739 : ∀ X0 : G, (M.op x (σ y)) = (σ (M.op (M.op y y) y)) ∨ (k X0 (M.op y y)) = X0 ∨ y = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e25588
               have i₂ := b4e92 (M.op y y) X0 y
               grind)
            | exact superpose b4e92 b4e25588
            | (have j1 := b4e92 (M.op y y) X0 y
               grind)
            | exact resolve b4e25588 b4e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92
          have b4e30760 : (M.op x (σ y)) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) ∨ (k y (M.op y y)) = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b4e25588
               have i₂ := b4e5877 y (M.op y y)
               grind)
            | exact superpose b4e5877 b4e25588
            | (have j1 := b4e5877 y (M.op y y)
               grind)
            | exact resolve b4e25588 b4e5877
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5877 b4e25588
          have b4e30802 : (M.op x (σ y)) = (σ (M.op y (M.op y y))) ∨ (k y (M.op y y)) = (M.op y (M.op y y)) := by
            first
            | (have r₁ := b4e30760
               have r₂ := b4e21
               grind)
            | exact resolve b4e30760 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30760
          have b4e30813 : ∀ X0 : G, (M.op x (σ y)) = (σ (M.op (M.op y y) y)) ∨ (k X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have j0 := b4e30739 X0
               grind)
            | (have r₁ := b4e30739 X0
               have r₂ := b4e21
               grind)
            | exact resolve b4e30739 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30739
          have b4e30823 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (k y (M.op y y)) = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b4e30802
               have i₂ := b4e50 y y
               grind)
            | exact superpose b4e50 b4e30802
            | exact resolve b4e30802 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30802
          have b4e30832 : ∀ X0 : G, (σ (M.op x y)) = (M.op x (σ y)) ∨ (k X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e30813 X0
               have i₂ := b4e178 y y
               grind)
            | exact superpose b4e178 b4e30813
            | (have j0 := b4e30813 X0
               grind)
            | exact resolve b4e30813 b4e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e178 b4e30813
          have b4e30836 : (k y (M.op y y)) = (M.op y (M.op y y)) := by
            first
            | (have r₁ := b4e30823
               have r₂ := b4e122
               grind)
            | exact resolve b4e30823 b4e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30823
          have b4e30841 : ∀ X0 : G, (k X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have j0 := b4e30832 X0
               grind)
            | (have r₁ := b4e30832 X0
               have r₂ := b4e122
               grind)
            | exact resolve b4e30832 b4e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e122 b4e30832
          have b4e30843 : (M.op x y) = (k y (M.op y y)) := by
            first
            | (have i₁ := b4e30836
               have i₂ := b4e50 y y
               grind)
            | exact superpose b4e50 b4e30836
            | exact resolve b4e30836 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50 b4e30836
          have b4e30848 : y = (M.op x y) := by
            first
            | (have i₁ := b4e30843
               have i₂ := b4e30841 y
               grind)
            | exact superpose b4e30841 b4e30843
            | exact resolve b4e30843 b4e30841
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30841 b4e30843
          have b4e31283 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e190 y x
               have i₂ := b4e30848
               grind)
            | exact superpose b4e30848 b4e190
            | exact resolve b4e190 b4e30848
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e190 b4e30848
          have b4e31870 : y ≠ y := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e31283 y
               grind)
            | exact superpose b4e31283 b4e21
            | (have r₁ := b4e21
               have r₂ := b4e31283 y
               grind)
            | exact resolve b4e21 b4e31283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31283
          have b4e31871 : False := by grind
          exact b4e31871
        · have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b5e75 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ x)
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
          have b5e91 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e75 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75
          have b5e95 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e91 X0
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e91
            | (have j0 := b5e91 X0
               grind)
            | exact resolve b5e91 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e91
          have b5e381 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have j0 := b5e95 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95
          have b5e382 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e381
          have b5e387 : False := by grind
          exact b5e387
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b6e82 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
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
        have b6e89 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e82 X0
             grind)
          | (have r₁ := b6e82 y
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
        have b6e5417 : y ≠ y ∨ y = (M.op y y) := by
          first
          | (have j0 := b6e89 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e5418 : y = (M.op y y) := by grind
        clear b6e5417
        have b6e5427 : False := by grind
        exact b6e5427
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b7e69 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
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
          have b7e90 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e69 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e4203 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e90 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e4204 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e4203 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4203
          have b7e4205 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e4204 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4204
          have b7e6703 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e34 x
               have i₂ := b7e4205 x
               grind)
            | exact superpose b7e4205 b7e34
            | (have j1 := b7e4205 x
               grind)
            | exact resolve b7e34 b7e4205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e4205
          have b7e6705 : x = (M.op x x) := by grind
          clear b7e6703
          have b7e6757 : False := by grind
          exact b7e6757
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e32 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X0 X1 x
               have i₂ := b8e13 X2 X1 x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e64 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ x) X0
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 X0 (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) x
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e64 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e338 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X0 X0 X2
               have i₂ := b8e68 X0
               grind)
            | exact superpose b8e68 b8e32
            | (have j1 := b8e68 X0
               grind)
            | exact resolve b8e32 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e20522 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e338 (σ y) (σ y) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e338 (σ y) X0 (σ y)
               grind)
            | exact superpose b8e338 b8e23
            | (have j1 := b8e338 (σ y) x x
               grind)
            | exact resolve b8e23 b8e338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e20550 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (σ x) X1) = (k (σ x) X1) ∨ (M.op (σ x) X1) = (k (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e68 X1
               have i₂ := b8e338 X1 X1 X0
               grind)
            | (have i₁ := b8e68 X1
               have i₂ := b8e338 X1 X0 X1
               grind)
            | exact superpose b8e338 b8e68
            | (have j0 := b8e68 X1
               have j1 := b8e338 X1 X1 x
               grind)
            | exact resolve b8e68 b8e338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68 b8e338
          have b8e20857 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (σ x) X1) = (k (σ x) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e20550 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20550
          have b8e20879 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j1 := b8e20857 x (σ y)
               grind)
            | (have r₁ := b8e20522 x
               have r₂ := b8e20857 x (σ y)
               grind)
            | exact resolve b8e20522 b8e20857
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20522 b8e20857
          have b8e20885 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e20879
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e20879
            | exact resolve b8e20879 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20879
          have b8e23072 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e20885
               grind)
            | exact superpose b8e20885 b8e20
            | exact resolve b8e20 b8e20885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20885
          have b8e23970 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e23072
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e23072
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e23072 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23072
          have b8e23984 : y = (M.op y y) ∨ x = (M.op x x) := by grind
          clear b8e23970
          have b8e23990 : x = (M.op x x) := by
            first
            | (have r₁ := b8e23984
               have r₂ := b8e21
               grind)
            | exact resolve b8e23984 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23984
          have b8e23991 : False := by grind
          exact b8e23991

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_x_pxx_pxy_Equation4494 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
        have b0e24 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e19
          | exact resolve b0e19 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e25 : (σ y) ≠ (σ y) := by
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
        have b0e26 : False := by grind
        exact b0e26
      · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
        · have b1e23 : y ≠ (M.op y y) := by grind
          have b1e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e26 : False := by grind
          exact b1e26
        · have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op x y) := by grind
          have b2e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e20
            | exact resolve b2e20 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e27 : (σ y) ≠ (σ y) := by
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
          have b2e28 : False := by grind
          exact b2e28
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : y = (M.op x y) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e27 : y ≠ y ∨ x = (k x y) := by
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
          have b3e31 : x = (k x y) := by grind
          clear b3e27
          have b3e78 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          have b3e82 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e78
               have r₂ := b3e22
               grind)
            | exact resolve b3e78 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e78
          have b3e83 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b3e82
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e82
            | exact resolve b3e82 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e82
          have b3e84 : (σ x) = (σ y) := by
            first
            | (have i₁ := b3e83
               have i₂ := b3e31
               grind)
            | exact superpose b3e31 b3e83
            | exact resolve b3e83 b3e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e31 b3e83
          have b3e85 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b3e23
               have i₂ := b3e84
               grind)
            | exact superpose b3e84 b3e23
            | exact resolve b3e23 b3e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e86 : (σ y) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e84
               grind)
            | exact superpose b3e84 b3e22
            | exact resolve b3e22 b3e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e84
          have b3e93 : False := by grind
          exact b3e93
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b4e25 : y ≠ (M.op y y) := by grind
            have b4e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : False := by grind
            exact b4e28
          · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op x y) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            have b5e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e29 : y ≠ y ∨ x = (k x y) := by
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
            have b5e31 : x = (k x y) := by grind
            clear b5e29
            have b5e77 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
            have b5e81 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e77
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e77 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e77
            have b5e82 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b5e81
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e81
              | exact resolve b5e81 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e81
            have b5e83 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e82
                 have i₂ := b5e31
                 grind)
              | exact superpose b5e31 b5e82
              | exact resolve b5e82 b5e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e31 b5e82
            have b5e84 : (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b5e24
                 have i₂ := b5e83
                 grind)
              | exact superpose b5e83 b5e24
              | exact resolve b5e24 b5e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e85 : (σ y) ≠ (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e83
                 grind)
              | exact superpose b5e83 b5e23
              | exact resolve b5e23 b5e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e83
            have b5e92 : False := by grind
            exact b5e92
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op x y) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e27 : y ≠ y ∨ x = (k x y) := by
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
          have b6e28 : y ≠ y ∨ y = (k y y) := by
            first
            | (have i₁ := b6e16 y y
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e16
            | (have j0 := b6e16 y y
               grind)
            | (have r₁ := b6e16 y y
               have r₂ := b6e24
               grind)
            | exact resolve b6e16 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e29 : y = (k y y) := by grind
          clear b6e28
          have b6e30 : x = (k x y) := by grind
          clear b6e27
          have b6e35 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e13 x X1 X3
               have i₂ := b6e13 x X1 X0
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X0 X1
               have i₂ := b6e18 (σ X0) (σ X1)
               grind)
            | exact superpose b6e18 b6e19
            | (have j1 := b6e18 (σ X0) (σ X1)
               grind)
            | exact resolve b6e19 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e59 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b6e1073 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b6e59 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e59
          have b6e1074 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b6e1073
               have r₂ := b6e22
               grind)
            | exact resolve b6e1073 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1073
          have b6e1075 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b6e1074
               have i₂ := b6e19 x y
               grind)
            | exact superpose b6e19 b6e1074
            | exact resolve b6e1074 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1074
          have b6e1076 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e1075
               have i₂ := b6e30
               grind)
            | exact superpose b6e30 b6e1075
            | exact resolve b6e1075 b6e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e30 b6e1075
          have b6e1079 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e1076
               grind)
            | exact superpose b6e1076 b6e22
            | exact resolve b6e22 b6e1076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e1084 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e35 X0 (σ y) (σ x)
               have i₂ := b6e1076
               grind)
            | exact superpose b6e1076 b6e35
            | exact resolve b6e35 b6e1076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e35
          have b6e1094 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e1084 X0
               have i₂ := b6e1076
               grind)
            | exact superpose b6e1076 b6e1084
            | exact resolve b6e1084 b6e1076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1076 b6e1084
          have b6e1542 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b6e52 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e52
          have b6e1544 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b6e1542 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1542
          have b6e7292 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b6e1544 y
               have i₂ := b6e29
               grind)
            | exact superpose b6e29 b6e1544
            | (have j0 := b6e1544 y
               grind)
            | exact resolve b6e1544 b6e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e29 b6e1544
          have b6e7299 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b6e7292
          have b6e10313 : (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b6e1094 (σ y)
               have i₂ := b6e7299
               grind)
            | exact superpose b6e7299 b6e1094
            | exact resolve b6e1094 b6e7299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1094
          have b6e10395 : (σ x) = (σ y) := by
            first
            | (have i₁ := b6e10313
               have i₂ := b6e7299
               grind)
            | exact superpose b6e7299 b6e10313
            | exact resolve b6e10313 b6e7299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e7299 b6e10313
          have b6e10405 : False := by grind
          exact b6e10405
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b7e25 : y ≠ (M.op y y) := by grind
            have b7e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : False := by grind
            exact b7e28
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b8e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op x y) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b8e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e29 : y ≠ y ∨ x = (k x y) := by
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
            have b8e30 : x = (k x y) := by grind
            clear b8e29
            have b8e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
            have b8e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
            have b8e34 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
              intro X0 X1 X3
              first
              | (have i₁ := b8e14 x X1 X3
                 have i₂ := b8e14 x X1 X0
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e36 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y y)) := by
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
            have b8e39 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X0 X1 x
                 have i₂ := b8e14 X2 X1 x
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e40 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X2 (M.op X1 X1) x
                 have i₂ := b8e14 (M.op x (M.op X1 X1)) X1 X0
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e41 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X2 (M.op X1 X1)) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e17 X2 (M.op X1 X1)
                 have i₂ := b8e14 X2 X1 X0
                 grind)
              | exact superpose b8e14 b8e17
              | (have j0 := b8e17 X2 (M.op X1 X1)
                 grind)
              | exact resolve b8e17 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e45 : ∀ X1 : G, (M.op y y) = (M.op (M.op X1 y) y) := by
              intro X1
              first
              | (have i₁ := b8e14 x y X1
                 have i₂ := b8e36 x
                 grind)
              | exact superpose b8e36 b8e14
              | exact resolve b8e14 b8e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e48 : ∀ X0 : G, (M.op y y) ≠ (M.op y y) ∨ (k X0 (M.op y y)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e17 X0 (M.op y y)
                 have i₂ := b8e36 X0
                 grind)
              | exact superpose b8e36 b8e17
              | (have j0 := b8e17 X0 (M.op y y)
                 grind)
              | (have r₁ := b8e17 X0 (M.op y y)
                 have r₂ := b8e36 X0
                 grind)
              | exact resolve b8e17 b8e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e36
            have b8e50 : ∀ X0 : G, (k X0 (M.op y y)) = X0 := by
              intro X0
              first
              | (have j0 := b8e48 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e48
            have b8e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
            have b8e61 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 X2) X2) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X1 X2 X3
                 have i₂ := b8e19 X2 X0
                 grind)
              | (have i₁ := b8e14 X0 X1 X2
                 have i₂ := b8e19 X0 (M.op X1 X1)
                 grind)
              | exact superpose b8e19 b8e14
              | (have j1 := b8e19 X2 X0
                 grind)
              | exact resolve b8e14 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
            have b8e88 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b8e15 (k (τ X0) X1)
                 have i₂ := b8e31 X0 X1
                 grind)
              | exact superpose b8e31 b8e15
              | exact resolve b8e15 b8e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e31
            have b8e153 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e88 X1 (τ X0)
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e88
              | exact resolve b8e88 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e88
            have b8e333 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e40 X2 X1 X3
                 have i₂ := b8e39 (M.op X1 X1) X1 X0
                 grind)
              | (have i₁ := b8e40 X2 X1 X3
                 have i₂ := b8e39 X0 X1 (M.op X1 X1)
                 grind)
              | exact superpose b8e39 b8e40
              | exact resolve b8e40 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e39
            have b8e1103 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have j0 := b8e66 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e66
            have b8e1104 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b8e1103
                 have r₂ := b8e23
                 grind)
              | exact resolve b8e1103 b8e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1103
            have b8e1105 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e1104
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e1104
              | exact resolve b8e1104 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1104
            have b8e1106 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b8e1105
                 have i₂ := b8e30
                 grind)
              | exact superpose b8e30 b8e1105
              | exact resolve b8e1105 b8e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e30 b8e1105
            have b8e1114 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e34 X0 (σ y) (σ x)
                 have i₂ := b8e1106
                 grind)
              | exact superpose b8e1106 b8e34
              | exact resolve b8e34 b8e1106
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e34
            have b8e1127 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e1114 X0
                 have i₂ := b8e1106
                 grind)
              | exact superpose b8e1106 b8e1114
              | exact resolve b8e1114 b8e1106
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1106 b8e1114
            have b8e1317 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1 X2
              first
              | (have j0 := b8e61 X1 X1 X0 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e61
            have b8e1515 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op X2 (M.op (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e40 X0 (σ X1) X2
                 have i₂ := b8e59 X1 X1
                 grind)
              | exact superpose b8e59 b8e40
              | (have j1 := b8e59 X0 X0
                 grind)
              | exact resolve b8e40 b8e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e40
            have b8e1575 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b8e59 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e59
            have b8e1577 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b8e1575 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1575
            have b8e1582 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op X2 (M.op (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0 X1 X2
              first
              | (have j0 := b8e1515 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1515
            have b8e7628 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
              first
              | (have i₁ := b8e1577 (M.op y y)
                 have i₂ := b8e50 (M.op y y)
                 grind)
              | exact superpose b8e50 b8e1577
              | (have j0 := b8e1577 (M.op y y)
                 grind)
              | exact resolve b8e1577 b8e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e50
            have b8e7657 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0
              first
              | (have i₁ := b8e1577 (τ X0)
                 have i₂ := b8e32 X0 (τ X0)
                 grind)
              | exact superpose b8e32 b8e1577
              | (have j0 := b8e1577 (τ X0)
                 grind)
              | exact resolve b8e1577 b8e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e32 b8e1577
            have b8e7683 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
            clear b8e7628
            have b8e7692 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0
              first
              | (have i₁ := b8e7657 X0
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e7657
              | (have j0 := b8e7657 X0
                 grind)
              | exact resolve b8e7657 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7657
            have b8e7706 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b8e7692 X0
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e7692
              | (have j0 := b8e7692 X0
                 grind)
              | exact resolve b8e7692 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7692
            have b8e16527 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
              intro X0
              first
              | (have i₁ := b8e7706 (τ X0)
                 have i₂ := b8e153 X0 X0
                 grind)
              | exact superpose b8e153 b8e7706
              | (have j0 := b8e7706 (τ X0)
                 grind)
              | exact resolve b8e7706 b8e153
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e153 b8e7706
            have b8e19847 : ∀ X1 : G, (M.op y y) ≠ X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op y X1) = X1 := by
              intro X1
              first
              | (have i₁ := b8e1317 y X1 x
                 have i₂ := b8e45 x
                 grind)
              | exact superpose b8e45 b8e1317
              | (have j0 := b8e1317 y X1 x
                 grind)
              | (have r₁ := b8e1317 y (M.op y y) X1
                 have r₂ := b8e45 X1
                 grind)
              | exact resolve b8e1317 b8e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1317
            have b8e19943 : ∀ X1 : G, (M.op y X1) = (k y X1) ∨ (M.op y X1) = X1 := by
              intro X1
              first
              | (have j0 := b8e19847 X1
                 have j1 := b8e19 y X1
                 grind)
              | (have r₁ := b8e19847 (k y y)
                 have r₂ := b8e19 y y
                 grind)
              | (have r₁ := b8e19847 X1
                 have r₂ := b8e19 y X1
                 grind)
              | (have r₁ := b8e19847 (M.op x x)
                 have r₂ := b8e19 x (M.op y y)
                 grind)
              | exact resolve b8e19847 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e19847
            have b8e114556 : ∀ X0 X1 : G, (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op X0 (M.op X1 (σ (M.op y y)))) := by
              intro X0 X1
              first
              | (have i₁ := b8e333 X0 (σ (M.op y y)) (σ (M.op y y)) x
                 have i₂ := b8e7683
                 grind)
              | exact superpose b8e7683 b8e333
              | exact resolve b8e333 b8e7683
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e333
            have b8e114640 : ∀ X0 X1 : G, (σ (M.op y y)) = (M.op X0 (M.op X1 (σ (M.op y y)))) := by
              intro X0 X1
              first
              | (have i₁ := b8e114556 X0 X1
                 have i₂ := b8e7683
                 grind)
              | exact superpose b8e7683 b8e114556
              | exact resolve b8e114556 b8e7683
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7683 b8e114556
            have b8e151852 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op X1 (M.op (σ (M.op y y)) (σ (M.op y y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
              intro X0 X1
              first
              | (have i₁ := b8e1582 y X1 x
                 have i₂ := b8e19943 y
                 grind)
              | exact superpose b8e19943 b8e1582
              | (have j0 := b8e1582 y X1 x
                 have j1 := b8e19943 y
                 grind)
              | exact resolve b8e1582 b8e19943
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1582 b8e19943
            have b8e152792 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op X1 (M.op (σ (M.op y y)) (σ (M.op y y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              intro X0 X1
              first
              | (have j0 := b8e151852 X0 X1
                 grind)
              | (have r₁ := b8e151852 X0 X1
                 have r₂ := b8e26
                 grind)
              | exact resolve b8e151852 b8e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e151852
            have b8e152845 : ∀ X0 : G, (σ (M.op y y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e152792 X0 x
                 have i₂ := b8e114640 x (σ (M.op y y))
                 grind)
              | exact superpose b8e114640 b8e152792
              | exact resolve b8e152792 b8e114640
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e114640 b8e152792
            have b8e152851 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
              first
              | (have i₁ := b8e152845 x
                 have i₂ := b8e1127 x
                 grind)
              | exact superpose b8e1127 b8e152845
              | exact resolve b8e152845 b8e1127
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1127 b8e152845
            have b8e472955 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (σ (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b8e41 (σ y) (σ y) x
                 have i₂ := b8e152851
                 grind)
              | exact superpose b8e152851 b8e41
              | exact resolve b8e41 b8e152851
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e41
            have b8e473027 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (σ (M.op y y)) := by
              intro X0
              first
              | (have j0 := b8e472955 X0
                 grind)
              | (have r₁ := b8e472955 X0
                 have r₂ := b8e152851
                 grind)
              | exact resolve b8e472955 b8e152851
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e152851 b8e472955
            have b8e474627 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
              first
              | (have i₁ := b8e16527 (σ y)
                 have i₂ := b8e473027 (σ y)
                 grind)
              | exact superpose b8e473027 b8e16527
              | (have j0 := b8e16527 (σ y)
                 grind)
              | exact resolve b8e16527 b8e473027
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e16527 b8e473027
            have b8e474650 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (σ (M.op y y)) := by grind
            clear b8e474627
            have b8e474662 : y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
              first
              | (have i₁ := b8e474650
                 have i₂ := b8e15 y
                 grind)
              | exact superpose b8e15 b8e474650
              | exact resolve b8e474650 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e474650
            have b8e474670 : (σ x) = (σ (M.op y y)) := by
              first
              | (have r₁ := b8e474662
                 have r₂ := b8e26
                 grind)
              | exact resolve b8e474662 b8e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e474662
            have b8e475761 : (M.op y y) = (τ (σ x)) := by
              first
              | (have i₁ := b8e15 (M.op y y)
                 have i₂ := b8e474670
                 grind)
              | exact superpose b8e474670 b8e15
              | exact resolve b8e15 b8e474670
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e474670
            have b8e475818 : x = (M.op y y) := by
              first
              | (have i₁ := b8e475761
                 have i₂ := b8e15 x
                 grind)
              | exact superpose b8e15 b8e475761
              | exact resolve b8e475761 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e475761
            have b8e476926 : x ≠ y := by
              first
              | (have i₁ := b8e26
                 have i₂ := b8e475818
                 grind)
              | exact superpose b8e475818 b8e26
              | exact resolve b8e26 b8e475818
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e476986 : x = (M.op x y) := by
              first
              | (have i₁ := b8e45 y
                 have i₂ := b8e475818
                 grind)
              | exact superpose b8e475818 b8e45
              | exact resolve b8e45 b8e475818
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e45 b8e475818
            have b8e477564 : x = y := by
              first
              | (have i₁ := b8e476986
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e476986
              | exact resolve b8e476986 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e476986
            have b8e477687 : False := by grind
            exact b8e477687
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
            intro X0 X1 X2
            grind
          have b9e21 : y ≠ (M.op x y) := by grind
          have b9e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e50 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b9e13 X0 y y
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e13
            | exact resolve b9e13 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e55 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b9e50 X0
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e50
            | exact resolve b9e50 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e50
          have b9e63 : y ≠ y := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e55 x
               grind)
            | exact superpose b9e55 b9e21
            | (have r₁ := b9e21
               have r₂ := b9e55 x
               grind)
            | exact resolve b9e21 b9e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e55
          have b9e64 : False := by grind
          exact b9e64
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b10e25 : y ≠ (M.op y y) := by grind
            have b10e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e28 : False := by grind
            exact b10e28
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op x y) := by grind
            have b11e23 : y = (M.op x x) := by grind
            have b11e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
            have b11e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e30 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b11e31 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b11e30
            have b11e32 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b11e31
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e31
              | exact resolve b11e31 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e31
            have b11e33 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e32
                 grind)
              | exact superpose b11e32 b11e15
              | exact resolve b11e15 b11e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e32
            have b11e34 : x = (k x y) := by
              first
              | (have i₁ := b11e33
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e33
              | exact resolve b11e33 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33
            have b11e78 : y = (k x y) ∨ y = (M.op x y) := by grind
            have b11e80 : y = (k x y) := by
              first
              | (have r₁ := b11e78
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e78 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e78
            have b11e83 : x = y := by
              first
              | (have i₁ := b11e34
                 have i₂ := b11e80
                 grind)
              | exact superpose b11e80 b11e34
              | exact resolve b11e34 b11e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e34 b11e80
            have b11e89 : y = (M.op y y) := by
              first
              | (have i₁ := b11e23
                 have i₂ := b11e83
                 grind)
              | exact superpose b11e83 b11e23
              | exact resolve b11e23 b11e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e83
            have b11e99 : False := by grind
            exact b11e99
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b12e22 : y ≠ (M.op x y) := by grind
            have b12e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e49 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b12e14 X0 y y
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e54 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b12e49 X0
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e49
              | exact resolve b12e49 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e49
            have b12e61 : y ≠ y := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e54 x
                 grind)
              | exact superpose b12e54 b12e22
              | (have r₁ := b12e22
                 have r₂ := b12e54 x
                 grind)
              | exact resolve b12e22 b12e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e54
            have b12e62 : False := by grind
            exact b12e62
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b13e27 : y ≠ (M.op y y) := by grind
              have b13e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : False := by grind
              exact b13e30
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                grind
              have b14e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : y = (M.op x x) := by grind
              have b14e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              have b14e28 : y ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e42 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
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
              have b14e43 : ∀ X0 : G, (M.op X0 y) = (M.op y x) := by
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
              have b14e64 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X0 X0 X0
                   have i₂ := b14e20 X0 X1
                   grind)
                | (have i₁ := b14e15 X0 X1 X2
                   have i₂ := b14e20 X0 (M.op X2 X1)
                   grind)
                | exact superpose b14e20 b14e15
                | (have j1 := b14e20 X2 X0
                   grind)
                | exact resolve b14e15 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e175 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e42 X0
                   have i₂ := b14e42 X1
                   grind)
                | exact superpose b14e42 b14e42
                | exact resolve b14e42 b14e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e180 : (σ y) ≠ (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b14e25
                   have i₂ := b14e42 (σ x)
                   grind)
                | exact superpose b14e42 b14e25
                | exact resolve b14e25 b14e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e355 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e180
                   have i₂ := b14e42 X0
                   grind)
                | exact superpose b14e42 b14e180
                | exact resolve b14e180 b14e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e42 b14e180
              have b14e1146 : ∀ X0 X1 : G, (M.op X0 (σ y)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op (σ y) X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e20 (σ y) X1
                   have i₂ := b14e175 (σ y) X0
                   grind)
                | (have i₁ := b14e20 (σ y) X1
                   have i₂ := b14e175 X0 (σ y)
                   grind)
                | exact superpose b14e175 b14e20
                | (have j0 := b14e20 (σ y) X1
                   grind)
                | exact resolve b14e20 b14e175
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e1167 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e22
                   have i₂ := b14e175 (σ x) X0
                   grind)
                | (have i₁ := b14e22
                   have i₂ := b14e175 X0 (σ x)
                   grind)
                | exact superpose b14e175 b14e22
                | exact resolve b14e22 b14e175
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e1169 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b14e1167 X0
                   have i₂ := b14e43 x
                   grind)
                | exact superpose b14e43 b14e1167
                | exact resolve b14e1167 b14e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1167
              have b14e1535 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e25
                   have i₂ := b14e64 (σ y) (σ x) X0
                   grind)
                | (have i₁ := b14e25
                   have i₂ := b14e64 (σ x) x (σ y)
                   grind)
                | exact superpose b14e64 b14e25
                | (have j1 := b14e64 (σ y) x X0
                   grind)
                | (have r₁ := b14e25
                   have r₂ := b14e64 (σ y) x (σ x)
                   grind)
                | exact resolve b14e25 b14e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e1617 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
                intro X0 X1
                first
                | (have j0 := b14e64 X0 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e64
              have b14e1632 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
                intro X0
                first
                | (have j0 := b14e1535 X0
                   grind)
                | (have r₁ := b14e1535 X0
                   have r₂ := b14e355 X0
                   grind)
                | exact resolve b14e1535 b14e355
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e355 b14e1535
              have b14e3429 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ (σ (M.op X0 y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e1169 X1
                   have i₂ := b14e43 X0
                   grind)
                | exact superpose b14e43 b14e1169
                | exact resolve b14e1169 b14e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e43 b14e1169
              have b14e20929 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e1617 (σ y) x
                   have i₂ := b14e175 x X0
                   grind)
                | (have i₁ := b14e1617 (σ y) x
                   have i₂ := b14e175 X0 x
                   grind)
                | exact superpose b14e175 b14e1617
                | (have j0 := b14e1617 (σ y) X0
                   grind)
                | exact resolve b14e1617 b14e175
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1617
              have b14e21003 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have j1 := b14e1146 (σ y) (σ y)
                   grind)
                | (have r₁ := b14e20929 x
                   have r₂ := b14e1146 x (σ y)
                   grind)
                | (have r₁ := b14e20929 (σ y)
                   have r₂ := b14e1146 x (σ y)
                   grind)
                | exact resolve b14e20929 b14e1146
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1146 b14e20929
              have b14e21034 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
                first
                | (have j1 := b14e1632 (σ y)
                   grind)
                | (have r₁ := b14e21003
                   have r₂ := b14e1632 (σ y)
                   grind)
                | exact resolve b14e21003 b14e1632
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1632 b14e21003
              have b14e21038 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
                first
                | (have i₁ := b14e21034
                   have i₂ := b14e21 y y
                   grind)
                | exact superpose b14e21 b14e21034
                | exact resolve b14e21034 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e21034
              have b14e21883 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k y y)) := by
                intro X0
                first
                | (have i₁ := b14e175 X0 (σ y)
                   have i₂ := b14e21038
                   grind)
                | exact superpose b14e21038 b14e175
                | exact resolve b14e175 b14e21038
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e175 b14e21038
              have b14e23931 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
                intro X0
                first
                | (have i₁ := b14e21883 X0
                   have i₂ := b14e20 y y
                   grind)
                | exact superpose b14e20 b14e21883
                | (have j1 := b14e20 y y
                   grind)
                | exact resolve b14e21883 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e21883
              have b14e24113 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
                intro X0
                first
                | (have j0 := b14e23931 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e23931
              have b14e24171 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op y y)) := by
                intro X0
                first
                | (have j0 := b14e24113 X0
                   grind)
                | (have r₁ := b14e24113 X0
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e24113 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e24113
              have b14e24199 : False := by grind
              exact b14e24199
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b15e22 : y ≠ (M.op x y) := by grind
            have b15e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e45 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b15e14 X0 y y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e14
              | exact resolve b15e14 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e50 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b15e45 X0
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e45
              | exact resolve b15e45 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e45
            have b15e57 : y ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e50 x
                 grind)
              | exact superpose b15e50 b15e22
              | (have r₁ := b15e22
                 have r₂ := b15e50 x
                 grind)
              | exact resolve b15e22 b15e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e50
            have b15e58 : False := by grind
            exact b15e58
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b16e27 : y ≠ (M.op y y) := by grind
              have b16e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e30 : False := by grind
              exact b16e30
            · have b17e19 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : y ≠ (M.op x y) := by grind
              have b17e24 : y = (M.op x x) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e62 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
              have b17e66 : y = (k x y) ∨ y = (M.op x y) := by grind
              have b17e68 : y = (k x y) := by
                first
                | (have r₁ := b17e66
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e66 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e66
              have b17e1407 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b17e62 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e62
              have b17e1408 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e1407
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e1407 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1407
              have b17e1409 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e1408
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e1408
                | exact resolve b17e1408 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1408
              have b17e1410 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b17e1409
                   have i₂ := b17e68
                   grind)
                | exact superpose b17e68 b17e1409
                | exact resolve b17e1409 b17e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e68 b17e1409
              have b17e1411 : False := by grind
              exact b17e1411
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
            intro X0 X1 X2
            grind
          have b18e21 : y ≠ (M.op x y) := by grind
          have b18e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e47 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
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
          have b18e52 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b18e47 X0
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e47
            | exact resolve b18e47 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e47
          have b18e59 : y ≠ y := by
            first
            | (have i₁ := b18e21
               have i₂ := b18e52 x
               grind)
            | exact superpose b18e52 b18e21
            | (have r₁ := b18e21
               have r₂ := b18e52 x
               grind)
            | exact resolve b18e21 b18e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e52
          have b18e60 : False := by grind
          exact b18e60
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b19e25 : y ≠ (M.op y y) := by grind
            have b19e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e28 : False := by grind
            exact b19e28
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e18 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b20e22 : y ≠ (M.op x y) := by grind
            have b20e23 : y ≠ (M.op x x) := by grind
            have b20e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
            have b20e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b20e21
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e21
              | exact resolve b20e21 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e29 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b20e30 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b20e29
            have b20e31 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b20e30
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e30
              | exact resolve b20e30 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e32 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e31
                 grind)
              | exact superpose b20e31 b20e15
              | exact resolve b20e15 b20e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31
            have b20e33 : x = (k x y) := by
              first
              | (have i₁ := b20e32
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e32
              | exact resolve b20e32 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e32
            have b20e34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
            have b20e36 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
            have b20e43 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) := by
              intro X0
              first
              | (have i₁ := b20e14 X0 (σ y) (σ x)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e14
              | exact resolve b20e14 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e45 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e14 X2 X1 (M.op x X1)
                 have i₂ := b20e14 X0 X1 x
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e47 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e14 X2 (M.op X1 X1) x
                 have i₂ := b20e14 (M.op x (M.op X1 X1)) X1 X0
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
            have b20e60 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b20e33
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e33
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e33 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e33
            have b20e62 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e14 X0 X0 X0
                 have i₂ := b20e19 X0 X1
                 grind)
              | (have i₁ := b20e14 X0 X1 X2
                 have i₂ := b20e19 X0 (M.op X2 X1)
                 grind)
              | exact superpose b20e19 b20e14
              | (have j1 := b20e19 X2 X0
                 grind)
              | exact resolve b20e14 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e67 : x = (M.op x y) ∨ y = (M.op x y) := by
              first
              | (have r₁ := b20e60
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e60 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e60
            have b20e70 : x = (M.op x y) := by
              first
              | (have r₁ := b20e67
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e67 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e67
            have b20e72 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b20e28
                 have i₂ := b20e70
                 grind)
              | exact superpose b20e70 b20e28
              | exact resolve b20e28 b20e70
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e73 : x ≠ y := by
              first
              | (have i₁ := b20e22
                 have i₂ := b20e70
                 grind)
              | exact superpose b20e70 b20e22
              | exact resolve b20e22 b20e70
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e74 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b20e14 X0 y x
                 have i₂ := b20e70
                 grind)
              | exact superpose b20e70 b20e14
              | exact resolve b20e14 b20e70
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e76 : ∀ X0 : G, x = (M.op X0 (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b20e74 X0
                 have i₂ := b20e70
                 grind)
              | exact superpose b20e70 b20e74
              | exact resolve b20e74 b20e70
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e70 b20e74
            have b20e78 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b20e80 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 := by
              intro X0 X1
              first
              | (have j0 := b20e78 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e78
            have b20e87 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b20e15 (k X0 (τ X1))
                 have i₂ := b20e36 X1 X0
                 grind)
              | exact superpose b20e36 b20e15
              | exact resolve b20e15 b20e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e36
            have b20e189 : ∀ X0 : G, x = (M.op X0 (M.op (M.op y y) (M.op y y))) := by
              intro X0
              first
              | (have i₁ := b20e14 X0 (M.op y y) x
                 have i₂ := b20e76 (M.op x (M.op y y))
                 grind)
              | exact superpose b20e76 b20e14
              | exact resolve b20e14 b20e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e190 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b20e189 X0
                 have i₂ := b20e76 (M.op y y)
                 grind)
              | exact superpose b20e76 b20e189
              | exact resolve b20e189 b20e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e189
            have b20e207 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k X0 (M.op (σ y) (σ y))) = X0 := by
              intro X0
              first
              | (have i₁ := b20e17 X0 (M.op (σ y) (σ y))
                 have i₂ := b20e43 X0
                 grind)
              | exact superpose b20e43 b20e17
              | (have j0 := b20e17 X0 (M.op (σ y) (σ y))
                 grind)
              | (have r₁ := b20e17 X0 (M.op (σ y) (σ y))
                 have r₂ := b20e43 X0
                 grind)
              | exact resolve b20e17 b20e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e43
            have b20e215 : ∀ X0 : G, (k X0 (M.op (σ y) (σ y))) = X0 := by
              intro X0
              first
              | (have j0 := b20e207 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e207
            have b20e227 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b20e17 X0 x
                 have i₂ := b20e190 X0
                 grind)
              | exact superpose b20e190 b20e17
              | (have j0 := b20e17 X0 x
                 grind)
              | (have r₁ := b20e17 X0 x
                 have r₂ := b20e190 X0
                 grind)
              | exact resolve b20e17 b20e190
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e190
            have b20e232 : ∀ X0 : G, (k X0 x) = X0 := by
              intro X0
              first
              | (have j0 := b20e227 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e227
            have b20e773 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (k (τ X0) X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b20e34 X0 X1
                 have i₂ := b20e80 X1 (τ X0)
                 grind)
              | exact superpose b20e80 b20e34
              | (have j1 := b20e80 X1 (τ X0)
                 grind)
              | exact resolve b20e34 b20e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e34 b20e80
            have b20e1012 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = X2 ∨ (M.op X0 X2) = X2 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e19 X0 X2
                 have i₂ := b20e62 X0 X0 X1
                 grind)
              | (have i₁ := b20e19 X2 X1
                 have i₂ := b20e62 X2 X1 X2
                 grind)
              | exact superpose b20e62 b20e19
              | (have j0 := b20e19 X1 X0
                 have j1 := b20e62 X0 X1 X1
                 grind)
              | exact resolve b20e19 b20e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1683 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k X0 X0))) = (M.op (M.op X2 (σ (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e45 X0 (σ X1) X2
                 have i₂ := b20e58 X1 X1
                 grind)
              | exact superpose b20e58 b20e45
              | (have j1 := b20e58 X0 X0
                 grind)
              | exact resolve b20e45 b20e58
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e45
            have b20e1738 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b20e58 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1740 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b20e1738 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1738
            have b20e1747 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k X0 X0))) = (M.op (M.op X2 (σ (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0 X1 X2
              first
              | (have j0 := b20e1683 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1683
            have b20e1798 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ y) (σ y)))) := by
              intro X0
              first
              | (have i₁ := b20e87 X0 (M.op (σ y) (σ y))
                 have i₂ := b20e215 (σ X0)
                 grind)
              | exact superpose b20e215 b20e87
              | exact resolve b20e87 b20e215
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e87 b20e215
            have b20e1816 : ∀ X0 : G, (k X0 (τ (M.op (σ y) (σ y)))) = X0 := by
              intro X0
              first
              | (have i₁ := b20e1798 X0
                 have i₂ := b20e15 X0
                 grind)
              | exact superpose b20e15 b20e1798
              | exact resolve b20e1798 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1798
            have b20e3433 : ∀ X0 : G, (k X0 (τ (σ (k y y)))) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              intro X0
              first
              | (have i₁ := b20e1816 X0
                 have i₂ := b20e58 y y
                 grind)
              | exact superpose b20e58 b20e1816
              | (have j1 := b20e58 y y
                 grind)
              | exact resolve b20e1816 b20e58
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e58
            have b20e3457 : ∀ X0 : G, (k X0 (τ (σ (k y y)))) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
              intro X0
              first
              | (have j0 := b20e3433 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e3433
            have b20e3463 : ∀ X0 : G, (k X0 (k y y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
              intro X0
              first
              | (have i₁ := b20e3457 X0
                 have i₂ := b20e15 (k y y)
                 grind)
              | exact superpose b20e15 b20e3457
              | exact resolve b20e3457 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e3457
            have b20e8068 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b20e1740 x
                 have i₂ := b20e232 x
                 grind)
              | exact superpose b20e232 b20e1740
              | (have j0 := b20e1740 x
                 grind)
              | exact resolve b20e1740 b20e232
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e232 b20e1740
            have b20e8075 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b20e8068
            have b20e8162 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op (σ x) (σ x))) := by
              intro X0
              first
              | (have i₁ := b20e47 (σ x) (σ x) x
                 have i₂ := b20e8075
                 grind)
              | exact superpose b20e8075 b20e47
              | exact resolve b20e47 b20e8075
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e47
            have b20e8199 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b20e8162 X0
                 have i₂ := b20e8075
                 grind)
              | exact superpose b20e8075 b20e8162
              | exact resolve b20e8162 b20e8075
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e8075 b20e8162
            have b20e187756 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b20e1012 X0 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1012
            have b20e187758 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b20e187756 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e187756
            have b20e187759 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b20e187758 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e187758
            have b20e326929 : ∀ X0 : G, (k X0 (M.op y y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              intro X0
              first
              | (have i₁ := b20e3463 X0
                 have i₂ := b20e19 y y
                 grind)
              | exact superpose b20e19 b20e3463
              | (have j1 := b20e19 (σ y) (σ y)
                 grind)
              | exact resolve b20e3463 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e3463
            have b20e326959 : ∀ X0 : G, (k X0 (M.op y y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
              intro X0
              first
              | (have j0 := b20e326929 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e326929
            have b20e326971 : ∀ X0 : G, (k X0 (M.op y y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
              intro X0
              first
              | (have j0 := b20e326959 X0
                 grind)
              | (have r₁ := b20e326959 X0
                 have r₂ := b20e26
                 grind)
              | exact resolve b20e326959 b20e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e326959
            have b20e374937 : (M.op y y) = (M.op (M.op y y) (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b20e187759 (M.op y y)
                 have i₂ := b20e326971 (M.op y y)
                 grind)
              | exact superpose b20e326971 b20e187759
              | (have j0 := b20e187759 (M.op y y)
                 grind)
              | exact resolve b20e187759 b20e326971
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e326971
            have b20e374953 : (M.op y y) = (M.op (M.op y y) (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b20e374937
            have b20e374971 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
              first
              | (have i₁ := b20e374953
                 have i₂ := b20e76 (M.op y y)
                 grind)
              | exact superpose b20e76 b20e374953
              | exact resolve b20e374953 b20e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e76 b20e374953
            have b20e377838 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ x = (M.op y y) := by
              intro X0
              first
              | (have i₁ := b20e1816 X0
                 have i₂ := b20e374971
                 grind)
              | exact superpose b20e374971 b20e1816
              | exact resolve b20e1816 b20e374971
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e374971
            have b20e378111 : ∀ X0 : G, (k X0 y) = X0 ∨ x = (M.op y y) := by
              intro X0
              first
              | (have i₁ := b20e377838 X0
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e377838
              | exact resolve b20e377838 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e377838
            have b20e380946 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
              first
              | (have i₁ := b20e187759 y
                 have i₂ := b20e378111 y
                 grind)
              | exact superpose b20e378111 b20e187759
              | (have j0 := b20e187759 y
                 grind)
              | exact resolve b20e187759 b20e378111
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e378111
            have b20e380983 : y = (M.op y y) ∨ x = (M.op y y) := by grind
            clear b20e380946
            have b20e381001 : x = (M.op y y) := by
              first
              | (have r₁ := b20e380983
                 have r₂ := b20e26
                 grind)
              | exact resolve b20e380983 b20e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e380983
            have b20e383131 : ∀ X0 : G, x = (M.op X0 y) ∨ x = (k y y) ∨ x = y := by
              intro X0
              first
              | (have i₁ := b20e62 y x y
                 have i₂ := b20e381001
                 grind)
              | exact superpose b20e381001 b20e62
              | exact resolve b20e62 b20e381001
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e62 b20e381001
            have b20e383396 : ∀ X0 : G, x = (M.op X0 y) ∨ x = (k y y) := by
              intro X0
              first
              | (have j0 := b20e383131 X0
                 grind)
              | (have r₁ := b20e383131 X0
                 have r₂ := b20e73
                 grind)
              | exact resolve b20e383131 b20e73
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e383131
            have b20e385890 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X1 (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op X2 y) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e1747 y X1 X2
                 have i₂ := b20e383396 X0
                 grind)
              | exact superpose b20e383396 b20e1747
              | (have j0 := b20e1747 y X1 X2
                 have j1 := b20e383396 X2
                 grind)
              | exact resolve b20e1747 b20e383396
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e383396
            have b20e385912 : ∀ X0 X2 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op X2 y) := by
              intro X0 X2
              first
              | (have i₁ := b20e385890 X0 x X2
                 have i₂ := b20e8199 x
                 grind)
              | exact superpose b20e8199 b20e385890
              | (have j0 := b20e385890 X0 x X2
                 grind)
              | exact resolve b20e385890 b20e8199
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e385890
            have b20e386103 : ∀ X2 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op X2 y) := by
              intro X2
              first
              | (have i₁ := b20e385912 x X2
                 have i₂ := b20e8199 x
                 grind)
              | exact superpose b20e8199 b20e385912
              | (have j0 := b20e385912 x X2
                 grind)
              | exact resolve b20e385912 b20e8199
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e385912
            have b20e386195 : ∀ X2 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op X2 y) := by
              intro X2
              first
              | (have i₁ := b20e386103 X2
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e386103
              | (have j0 := b20e386103 X2
                 grind)
              | exact resolve b20e386103 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e386103
            have b20e386224 : ∀ X2 : G, (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op X2 y) := by
              intro X2
              first
              | (have j0 := b20e386195 X2
                 grind)
              | (have r₁ := b20e386195 X2
                 have r₂ := b20e72
                 grind)
              | exact resolve b20e386195 b20e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e386195
            have b20e412850 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ x = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b20e1816 X0
                 have i₂ := b20e386224 X1
                 grind)
              | exact superpose b20e386224 b20e1816
              | (have j1 := b20e386224 X1
                 grind)
              | exact resolve b20e1816 b20e386224
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e386224
            have b20e413554 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ x = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b20e412850 X0 X1
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e412850
              | (have j0 := b20e412850 X0 X1
                 grind)
              | exact resolve b20e412850 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e412850
            have b20e417022 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b20e187759 y
                 have i₂ := b20e413554 y X0
                 grind)
              | exact superpose b20e413554 b20e187759
              | (have j0 := b20e187759 y
                 have j1 := b20e413554 X0 X0
                 grind)
              | exact resolve b20e187759 b20e413554
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e413554
            have b20e417403 : ∀ X0 : G, y = (M.op y y) ∨ x = (M.op X0 y) := by
              intro X0
              first
              | (have j0 := b20e417022 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e417022
            have b20e417599 : ∀ X0 : G, x = (M.op X0 y) := by
              intro X0
              first
              | (have j0 := b20e417403 X0
                 grind)
              | (have r₁ := b20e417403 X0
                 have r₂ := b20e26
                 grind)
              | exact resolve b20e417403 b20e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e417403
            have b20e420258 : ∀ X0 : G, (σ x) = (k X0 (σ y)) ∨ x = y ∨ y = (k (τ X0) y) := by
              intro X0
              first
              | (have i₁ := b20e773 X0 y
                 have i₂ := b20e417599 (τ X0)
                 grind)
              | exact superpose b20e417599 b20e773
              | (have j0 := b20e773 X0 y
                 grind)
              | exact resolve b20e773 b20e417599
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e773 b20e417599
            have b20e420267 : ∀ X0 : G, y = (k (τ X0) y) ∨ (σ x) = (k X0 (σ y)) := by
              intro X0
              first
              | (have j0 := b20e420258 X0
                 grind)
              | (have r₁ := b20e420258 X0
                 have r₂ := b20e73
                 grind)
              | exact resolve b20e420258 b20e73
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e73 b20e420258
            have b20e457974 : ∀ X0 : G, y = (k X0 y) ∨ (σ x) = (k (σ X0) (σ y)) := by
              intro X0
              first
              | (have i₁ := b20e420267 (σ X0)
                 have i₂ := b20e15 X0
                 grind)
              | exact superpose b20e15 b20e420267
              | (have j0 := b20e420267 (σ X0)
                 grind)
              | exact resolve b20e420267 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e420267
            have b20e458019 : ∀ X0 : G, (σ x) = (σ (k X0 y)) ∨ y = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b20e457974 X0
                 have i₂ := b20e20 X0 y
                 grind)
              | exact superpose b20e20 b20e457974
              | (have j0 := b20e457974 X0
                 grind)
              | exact resolve b20e457974 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e457974
            have b20e461646 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X1 (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
              intro X0 X1
              first
              | (have i₁ := b20e1747 y X1 x
                 have i₂ := b20e458019 y
                 grind)
              | exact superpose b20e458019 b20e1747
              | (have j0 := b20e1747 y X1 x
                 have j1 := b20e458019 y
                 grind)
              | exact resolve b20e1747 b20e458019
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1747 b20e458019
            have b20e461711 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
              intro X0
              first
              | (have i₁ := b20e461646 X0 x
                 have i₂ := b20e8199 x
                 grind)
              | exact superpose b20e8199 b20e461646
              | exact resolve b20e461646 b20e8199
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e461646
            have b20e461725 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
              first
              | (have i₁ := b20e461711 x
                 have i₂ := b20e8199 x
                 grind)
              | exact superpose b20e8199 b20e461711
              | exact resolve b20e461711 b20e8199
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e8199 b20e461711
            have b20e461735 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
              first
              | (have i₁ := b20e461725
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e461725
              | exact resolve b20e461725 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e461725
            have b20e461736 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
              first
              | (have r₁ := b20e461735
                 have r₂ := b20e72
                 grind)
              | exact resolve b20e461735 b20e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e72 b20e461735
            have b20e476070 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (k y y) := by
              intro X0
              first
              | (have i₁ := b20e1816 X0
                 have i₂ := b20e461736
                 grind)
              | exact superpose b20e461736 b20e1816
              | exact resolve b20e1816 b20e461736
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1816 b20e461736
            have b20e476312 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (k y y) := by
              intro X0
              first
              | (have i₁ := b20e476070 X0
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e476070
              | exact resolve b20e476070 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e476070
            have b20e478052 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b20e476312 y
                 have i₂ := b20e187759 y
                 grind)
              | exact superpose b20e187759 b20e476312
              | (have j1 := b20e187759 y
                 grind)
              | exact resolve b20e476312 b20e187759
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e187759 b20e476312
            have b20e478179 : y = (M.op y y) := by grind
            clear b20e478052
            have b20e478191 : False := by grind
            exact b20e478191
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b21e22 : y ≠ (M.op x y) := by grind
            have b21e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e42 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b21e14 X0 y y
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e47 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b21e42 X0
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e42
              | exact resolve b21e42 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e42
            have b21e53 : y ≠ y := by
              first
              | (have i₁ := b21e22
                 have i₂ := b21e47 x
                 grind)
              | exact superpose b21e47 b21e22
              | (have r₁ := b21e22
                 have r₂ := b21e47 x
                 grind)
              | exact resolve b21e22 b21e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e47
            have b21e54 : False := by grind
            exact b21e54
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b22e27 : y ≠ (M.op y y) := by grind
              have b22e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e30 : False := by grind
              exact b22e30
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : y ≠ (M.op x y) := by grind
              have b23e24 : y ≠ (M.op x x) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b23e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e81 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
              have b23e86 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e81
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e81 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e81
              have b23e87 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b23e86
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e86
                | exact resolve b23e86 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e86
              have b23e91 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e87
                   grind)
                | exact superpose b23e87 b23e16
                | exact resolve b23e16 b23e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e87
              have b23e92 : y = (k x y) := by
                first
                | (have i₁ := b23e91
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e91
                | exact resolve b23e91 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e91
              have b23e134 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e92
                   grind)
                | exact superpose b23e92 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e92
              have b23e135 : y = (M.op x y) ∨ y = (M.op x x) := by grind
              clear b23e134
              have b23e137 : y = (M.op x x) := by
                first
                | (have r₁ := b23e135
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e135 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e135
              have b23e139 : False := by grind
              exact b23e139
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b24e22 : y ≠ (M.op x y) := by grind
            have b24e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e36 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
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
            have b24e43 : ∀ X0 : G, y = (M.op X0 y) := by
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
            have b24e49 : y ≠ y := by
              first
              | (have i₁ := b24e22
                 have i₂ := b24e43 x
                 grind)
              | exact superpose b24e43 b24e22
              | (have r₁ := b24e22
                 have r₂ := b24e43 x
                 grind)
              | exact resolve b24e22 b24e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e43
            have b24e50 : False := by grind
            exact b24e50
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b25e27 : y ≠ (M.op y y) := by grind
              have b25e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e30 : False := by grind
              exact b25e30
            · have b26e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : y ≠ (M.op x y) := by grind
              have b26e24 : y ≠ (M.op x x) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
              have b26e977 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b26e63 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e63
              have b26e978 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b26e977
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e977 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e977
              have b26e979 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e978
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e978
                | exact resolve b26e978 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e978
              have b26e982 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e979
                   grind)
                | exact superpose b26e979 b26e22
                | exact resolve b26e22 b26e979
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e979
              have b26e1293 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b26e982
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e982
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e982 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e982
              have b26e1294 : y = (M.op x x) ∨ y = (M.op x y) := by grind
              clear b26e1293
              have b26e1297 : y = (M.op x y) := by
                first
                | (have r₁ := b26e1294
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e1294 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1294
              have b26e1300 : False := by grind
              exact b26e1300

/-- `Equation4507`: `x ◇ (y ◇ z) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4507 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4507 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4507.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1 X2
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
      have b0e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 (τ X0) X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e17
        | exact resolve b0e17 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
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
      have b0e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e25 X0 X1
           grind)
        | exact superpose b0e25 b0e12
        | exact resolve b0e12 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X0 X0)) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X3 (M.op X0 X0) X1
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ y) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) X0 X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e11 X0 X1 X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) X1))) := by
        intro X0 X1
        grind
      have b0e46 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e39 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e39
        | exact resolve b0e39 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 : G, (M.op y x) = (M.op x (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e39 x (M.op X0 x)
           have i₂ := b0e39 X0 x
           grind)
        | exact superpose b0e39 b0e39
        | exact resolve b0e39 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : (M.op y x) = (M.op y y) := by
        first
        | (have i₁ := b0e47 x
           have i₂ := b0e39 y x
           grind)
        | exact superpose b0e39 b0e47
        | exact resolve b0e47 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e47
      have b0e54 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e51
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e51
        | exact resolve b0e51 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e51
      have b0e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b0e78 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 X2
           have i₂ := b0e16 X2 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X1 X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X2 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e95 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e102 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e35 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e35
        | exact resolve b0e35 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e124 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e38 (σ x) (M.op X0 x)
           have i₂ := b0e38 X0 x
           grind)
        | exact superpose b0e38 b0e38
        | exact resolve b0e38 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e142 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e124 x
           have i₂ := b0e38 (σ y) x
           grind)
        | exact superpose b0e38 b0e124
        | exact resolve b0e124 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e124
      have b0e151 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e142
           have i₂ := b0e102
           grind)
        | exact superpose b0e102 b0e142
        | exact resolve b0e142 b0e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e102 b0e142
      have b0e198 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 X0 x X1 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e40
        | exact resolve b0e40 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e372 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) y) = (M.op X0 (M.op x (M.op X1 X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e34 x X1 X2 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e34
        | exact resolve b0e34 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e483 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e372 X0 x x
           have i₂ := b0e198 X0 (M.op x x)
           grind)
        | exact superpose b0e198 b0e372
        | exact resolve b0e372 b0e198
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e372
      have b0e534 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) y) = (M.op X0 (M.op (M.op x X1) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 (M.op x X1) X2
           have i₂ := b0e198 (M.op X0 X0) X1
           grind)
        | exact superpose b0e198 b0e11
        | exact resolve b0e11 b0e198
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e198
      have b0e539 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x X1) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e534 X0 X1 X2
           have i₂ := b0e483 X0
           grind)
        | exact superpose b0e483 b0e534
        | exact resolve b0e534 b0e483
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e534
      have b0e564 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op y (M.op (M.op x y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e42 y x
           have i₂ := b0e54
           grind)
        | exact superpose b0e54 b0e42
        | exact resolve b0e42 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e597 : (M.op x y) = (k (M.op x y) (M.op y y)) := by
        first
        | (have i₁ := b0e564 x
           have i₂ := b0e539 y y x
           grind)
        | exact superpose b0e539 b0e564
        | exact resolve b0e564 b0e539
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e539 b0e564
      have b0e608 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b0e597
           have i₂ := b0e54
           grind)
        | exact superpose b0e54 b0e597
        | exact resolve b0e597 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e597
      have b0e2288 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e78 X1 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e2627 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e31 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e31
        | exact resolve b0e31 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e2931 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b0e95
      have b0e2947 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2931 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e2931
        | exact resolve b0e2931 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2931
      have b0e3272 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e71 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4111 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e71 y y
           have i₂ := b0e151
           grind)
        | exact superpose b0e151 b0e71
        | (have j0 := b0e71 x y
           grind)
        | exact resolve b0e71 b0e151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71
      have b0e4112 : y = (k y (τ (M.op (σ x) (σ y)))) := by
        first
        | (have i₁ := b0e2947 y
           have i₂ := b0e151
           grind)
        | exact superpose b0e151 b0e2947
        | exact resolve b0e2947 b0e151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e151 b0e2947
      have b0e4146 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
      clear b0e4111
      have b0e158467 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2288 y X0
           have i₂ := b0e483 y
           grind)
        | exact superpose b0e483 b0e2288
        | (have j0 := b0e2288 y X0
           grind)
        | (have r₁ := b0e2288 y (M.op y y)
           have r₂ := b0e483 y
           grind)
        | (have r₁ := b0e2288 y (M.op (M.op (M.op y y) (M.op y y)) y)
           have r₂ := b0e483 (M.op y y)
           grind)
        | exact resolve b0e2288 b0e483
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e483 b0e2288
      have b0e158534 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e158467 X0
           have j1 := b0e16 y X0
           grind)
        | (have r₁ := b0e158467 (k y y)
           have r₂ := b0e16 y y
           grind)
        | (have r₁ := b0e158467 x
           have r₂ := b0e16 y x
           grind)
        | (have r₁ := b0e158467 (M.op X0 X0)
           have r₂ := b0e16 X0 (M.op y y)
           grind)
        | exact resolve b0e158467 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e158467
      have b0e158708 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = (M.op y (τ X0)) := by
        intro X0
        first
        | (have i₁ := b0e26 X0 y
           have i₂ := b0e158534 (τ X0)
           grind)
        | exact superpose b0e158534 b0e26
        | (have j1 := b0e158534 (τ X0)
           grind)
        | exact resolve b0e26 b0e158534
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e158534
      have b0e253156 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e3272 (τ X0) (τ X1)
           have i₂ := b0e2627 X1 X0
           grind)
        | exact superpose b0e2627 b0e3272
        | (have j0 := b0e3272 (τ X0) (τ X1)
           grind)
        | exact resolve b0e3272 b0e2627
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2627 b0e3272
      have b0e253181 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e253156 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e253156
        | (have j0 := b0e253156 X0 X1
           grind)
        | exact resolve b0e253156 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e253156
      have b0e253185 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e253181 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e253181
        | (have j0 := b0e253181 X0 X1
           grind)
        | exact resolve b0e253181 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e253181
      have b0e253188 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e253185 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e253185
        | (have j0 := b0e253185 X0 X1
           grind)
        | exact resolve b0e253185 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e253185
      have b0e253189 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e253188 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e253188
        | (have j0 := b0e253188 X0 X1
           grind)
        | exact resolve b0e253188 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e253188
      have b0e253190 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e253189 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e253189
        | (have j0 := b0e253189 X0 X1
           grind)
        | exact resolve b0e253189 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e253189
      have b0e253191 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e253190 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e253190
        | (have j0 := b0e253190 X0 X1
           grind)
        | exact resolve b0e253190 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e253190
      have b0e460865 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op y X0)) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e158708 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e158708
        | exact resolve b0e158708 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e158708
      have b0e460877 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e460865 X0
           have i₂ := b0e17 y X0
           grind)
        | exact superpose b0e17 b0e460865
        | (have j0 := b0e460865 X0
           grind)
        | exact resolve b0e460865 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e460865
      have b0e495821 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e4146
           grind)
        | exact superpose b0e4146 b0e18
        | exact resolve b0e18 b0e4146
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e495884 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
      clear b0e4146
      have b0e504820 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e495821
           have i₂ := b0e460877 y
           grind)
        | exact superpose b0e460877 b0e495821
        | (have j1 := b0e460877 y
           grind)
        | exact resolve b0e495821 b0e460877
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e460877 b0e495821
      have b0e504821 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e504820
           have i₂ := b0e54
           grind)
        | exact superpose b0e54 b0e504820
        | exact resolve b0e504820 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e504820
      have b0e504822 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
      clear b0e504821
      have b0e504827 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e504822
           have i₂ := b0e54
           grind)
        | exact superpose b0e54 b0e504822
        | exact resolve b0e504822 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e504822
      have b0e505693 : y = (k y (τ (σ y))) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e4112
           have i₂ := b0e504827
           grind)
        | exact superpose b0e504827 b0e4112
        | exact resolve b0e4112 b0e504827
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4112 b0e504827
      have b0e505922 : y = (k y y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e505693
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e505693
        | exact resolve b0e505693 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e505693
      have b0e506706 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e253191 y y
           have i₂ := b0e505922
           grind)
        | exact superpose b0e505922 b0e253191
        | (have j0 := b0e253191 y y
           grind)
        | (have r₁ := b0e253191 y y
           have r₂ := b0e505922
           grind)
        | exact resolve b0e253191 b0e505922
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e253191 b0e505922
      have b0e506707 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
      clear b0e506706
      have b0e506708 : y = (M.op y y) ∨ y = (M.op x y) := by grind
      clear b0e506707
      have b0e506738 : y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e506708
           have i₂ := b0e54
           grind)
        | exact superpose b0e54 b0e506708
        | exact resolve b0e506708 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54 b0e506708
      have b0e506739 : y = (M.op x y) := by grind
      clear b0e506738
      have b0e508120 : y = (k y y) := by
        first
        | (have i₁ := b0e608
           have i₂ := b0e506739
           grind)
        | exact superpose b0e506739 b0e608
        | exact resolve b0e608 b0e506739
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e608
      have b0e511529 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e495884
           have i₂ := b0e508120
           grind)
        | exact superpose b0e508120 b0e495884
        | exact resolve b0e495884 b0e508120
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e495884 b0e508120
      have b0e511578 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear b0e511529
      have b0e515515 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e511578
           grind)
        | exact superpose b0e511578 b0e18
        | exact resolve b0e18 b0e511578
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e511578
      have b0e515790 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e515515
           have i₂ := b0e506739
           grind)
        | exact superpose b0e506739 b0e515515
        | exact resolve b0e515515 b0e506739
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e506739 b0e515515
      have b0e515791 : False := by grind
      exact b0e515791
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1 X2
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
        have b1e28 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X2 X0 (M.op X1 x)
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X0 X0)) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X3 (M.op X0 X0) X1
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op X0 (σ y)) := by
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
        have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X2 X3)) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X0 X0) X2 X3
             have i₂ := b1e12 X0 (M.op X0 X0) X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 x X0 X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X0 X1 X2
             have i₂ := b1e12 X0 X1 X3
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X0 (M.op X1 X2) X3
             have i₂ := b1e12 (M.op X0 X0) X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) X1))) := by
          intro X0 X1
          grind
        have b1e38 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 (M.op X1 X2))) = (M.op y (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e33 (M.op X0 X0) X1
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e33
          | exact resolve b1e33 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e33 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e33
          | exact resolve b1e33 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 : G, (M.op y x) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e33 x (M.op X0 x)
             have i₂ := b1e33 X0 x
             grind)
          | exact superpose b1e33 b1e33
          | exact resolve b1e33 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b1e41 x
             have i₂ := b1e33 y x
             grind)
          | exact superpose b1e33 b1e41
          | exact resolve b1e41 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e46 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e38 X0 x x
             have i₂ := b1e33 X0 (M.op x x)
             grind)
          | exact superpose b1e33 b1e38
          | exact resolve b1e38 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e48 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b1e45
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e45
          | exact resolve b1e45 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e45
        have b1e113 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (σ x) X1
             have i₂ := b1e30 X0
             grind)
          | exact superpose b1e30 b1e12
          | exact resolve b1e12 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e116 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op X1 (M.op X0 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 (M.op X0 X0) (σ x)
             have i₂ := b1e30 X0
             grind)
          | exact superpose b1e30 b1e12
          | exact resolve b1e12 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e123 : (M.op x y) = (M.op y (M.op x y)) := by
          first
          | (have i₁ := b1e46 y
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e46
          | exact resolve b1e46 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e160 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e34 X0 x X1 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e34
          | exact resolve b1e34 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e331 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y (M.op x y)
             have i₂ := b1e123
             grind)
          | exact superpose b1e123 b1e12
          | exact resolve b1e12 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123
        have b1e333 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e331 X0
             have i₂ := b1e160 X0 y
             grind)
          | exact superpose b1e160 b1e331
          | exact resolve b1e331 b1e160
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e331
        have b1e566 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have i₁ := b1e36 X0 (σ x)
             have i₂ := b1e30 X0
             grind)
          | exact superpose b1e30 b1e36
          | exact resolve b1e36 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e765 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) x) := by
          intro X0 X1
          first
          | (have i₁ := b1e160 (M.op X0 X0) x
             have i₂ := b1e32 X0 X1 x x
             grind)
          | exact superpose b1e32 b1e160
          | exact resolve b1e160 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e160
        have b1e828 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op (M.op (M.op X0 X0) X0) x) := by
          intro X0
          first
          | (have i₁ := b1e765 X0 x
             have i₂ := b1e28 X0 x X0
             grind)
          | (have i₁ := b1e765 (M.op x x) x
             have i₂ := b1e28 (M.op (M.op (M.op x x) (M.op x x)) x) x x
             grind)
          | exact superpose b1e28 b1e765
          | exact resolve b1e765 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e765
        have b1e899 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op X0 X0) X0) x) := by
          intro X0
          first
          | (have i₁ := b1e828 X0
             have i₂ := b1e333 X0
             grind)
          | exact superpose b1e333 b1e828
          | exact resolve b1e828 b1e333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e333 b1e828
        have b1e1171 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e28 X1 x X0
             have i₂ := b1e35 X0 X1 X1 x
             grind)
          | exact superpose b1e35 b1e28
          | exact resolve b1e28 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e35
        have b1e1293 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 (M.op X0 (σ y))) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e1171 X0 X1
             have i₂ := b1e116 X0 X0
             grind)
          | exact superpose b1e116 b1e1171
          | exact resolve b1e1171 b1e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116 b1e1171
        have b1e3479 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (σ y)) = (M.op X0 (M.op (σ x) (M.op X1 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e29 (σ x) X1 X2 X0
             have i₂ := b1e113 (M.op X0 X0) (σ x)
             grind)
          | exact superpose b1e113 b1e29
          | exact resolve b1e29 b1e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e3508 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e3479 X0 x x
             have i₂ := b1e113 X0 (M.op x x)
             grind)
          | exact superpose b1e113 b1e3479
          | exact resolve b1e3479 b1e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3479
        have b1e6335 : (M.op (σ x) y) = (M.op (M.op (σ x) (σ y)) x) := by
          first
          | (have i₁ := b1e899 (σ x)
             have i₂ := b1e30 (σ x)
             grind)
          | exact superpose b1e30 b1e899
          | exact resolve b1e899 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e899
        have b1e6390 : (M.op (σ x) y) = (M.op (σ y) x) := by
          first
          | (have i₁ := b1e6335
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e6335
          | exact resolve b1e6335 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6335
        have b1e6772 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op X0 (M.op (σ x) y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e34 X0 (σ y) X1 x
             have i₂ := b1e6390
             grind)
          | exact superpose b1e6390 b1e34
          | exact resolve b1e34 b1e6390
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e6390
        have b1e6781 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e6772 X0 X1
             have i₂ := b1e113 X0 y
             grind)
          | exact superpose b1e113 b1e6772
          | exact resolve b1e6772 b1e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6772
        have b1e7880 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
          intro X0
          first
          | (have i₁ := b1e1293 (σ x) X0
             have i₂ := b1e113 (σ x) (σ y)
             grind)
          | exact superpose b1e113 b1e1293
          | exact resolve b1e1293 b1e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1293
        have b1e8083 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e7880 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e7880
          | exact resolve b1e7880 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7880
        have b1e11475 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y)))) := by
          first
          | (have i₁ := b1e566 (M.op (σ x) (σ x))
             have i₂ := b1e8083 (σ y)
             grind)
          | exact superpose b1e8083 b1e566
          | exact resolve b1e566 b1e8083
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e566 b1e8083
        have b1e11479 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b1e11475
             have i₂ := b1e6781 (M.op (σ x) (σ x)) (σ y)
             grind)
          | exact superpose b1e6781 b1e11475
          | exact resolve b1e11475 b1e6781
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6781 b1e11475
        have b1e11625 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b1e11479
             have i₂ := b1e3508 (σ x)
             grind)
          | exact superpose b1e3508 b1e11479
          | exact resolve b1e11479 b1e3508
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11479
        have b1e11723 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (σ y)) := by
          first
          | (have i₁ := b1e11625
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e11625
          | exact resolve b1e11625 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11625
        have b1e11792 : (M.op (M.op (σ x) (σ x)) (σ y)) = (k (M.op (M.op (σ x) (σ x)) (σ y)) (σ y)) := by
          first
          | (have i₁ := b1e11723
             have i₂ := b1e113 (M.op (σ x) (σ x)) (σ x)
             grind)
          | exact superpose b1e113 b1e11723
          | exact resolve b1e11723 b1e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e113 b1e11723
        have b1e11828 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
          first
          | (have i₁ := b1e11792
             have i₂ := b1e3508 (σ x)
             grind)
          | exact superpose b1e3508 b1e11792
          | exact resolve b1e11792 b1e3508
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3508 b1e11792
        have b1e11847 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e11828
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e11828
          | exact resolve b1e11828 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11828
        have b1e11862 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e11847
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e11847
          | exact resolve b1e11847 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11847
        have b1e12787 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e11862
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e11862
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e11862 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11862
        have b1e12805 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b1e12787
        have b1e12822 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e12805
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e12805
          | exact resolve b1e12805 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48 b1e12805
        have b1e12827 : y = (M.op y y) := by
          first
          | (have r₁ := b1e12822
             have r₂ := b1e24
             grind)
          | exact resolve b1e12822 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12822
        have b1e14239 : y = (M.op x y) := by
          first
          | (have i₁ := b1e33 y y
             have i₂ := b1e12827
             grind)
          | exact superpose b1e12827 b1e33
          | exact resolve b1e33 b1e12827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e12827
        have b1e16808 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e14239
             grind)
          | exact superpose b1e14239 b1e24
          | exact resolve b1e24 b1e14239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e14239
        have b1e16834 : False := by grind
        exact b1e16834
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
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
        have b2e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
        have b2e92 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e1551 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e69 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69
        have b2e1552 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1551
             have r₂ := b2e22
             grind)
          | exact resolve b2e1551 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1551
        have b2e1553 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1552
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1552
          | exact resolve b2e1552 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1552
        have b2e1554 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1553
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1553
          | exact resolve b2e1553 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1553
        have b2e1556 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e1554
             grind)
          | exact superpose b2e1554 b2e22
          | exact resolve b2e22 b2e1554
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1554
        have b2e2730 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e92
        have b2e2746 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e2730 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e2730
          | exact resolve b2e2730 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2730
        have b2e2775 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e61 x x
             grind)
          | exact superpose b2e61 b2e21
          | (have j1 := b2e61 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e61 x y
             grind)
          | exact resolve b2e21 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e2874 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e2775
        have b2e24847 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e2874
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e2874
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e2874 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2874
        have b2e24848 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e24847
        have b2e24849 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e24848
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e24848
          | exact resolve b2e24848 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24848
        have b2e24850 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e24849
        have b2e24856 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e24850
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e24850
          | exact resolve b2e24850 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24850
        have b2e24866 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e2746 x
             have i₂ := b2e24856
             grind)
          | exact superpose b2e24856 b2e2746
          | exact resolve b2e2746 b2e24856
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2746 b2e24856
        have b2e24950 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e24866
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e24866
          | exact resolve b2e24866 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24866
        have b2e26292 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e24950
             grind)
          | exact superpose b2e24950 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e24950
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24950
        have b2e26293 : x = (M.op x x) ∨ x = y := by grind
        clear b2e26292
        have b2e26302 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e26293
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e26293
          | exact resolve b2e26293 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26293
        have b2e26303 : x = y := by grind
        clear b2e26302
        have b2e27689 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1556
             have i₂ := b2e26303
             grind)
          | exact superpose b2e26303 b2e1556
          | exact resolve b2e1556 b2e26303
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1556 b2e26303
        have b2e27693 : False := by grind
        exact b2e27693
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
        have b3e43 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ y) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (σ x) X0 X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e12 X0 X1 X3
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e110 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e43 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e43
          | exact resolve b3e43 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e145 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b3e46 (σ x) (M.op X0 x)
             have i₂ := b3e46 X0 x
             grind)
          | exact superpose b3e46 b3e46
          | exact resolve b3e46 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e153 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e145 x
             have i₂ := b3e46 (σ y) x
             grind)
          | exact superpose b3e46 b3e145
          | exact resolve b3e145 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46 b3e145
        have b3e157 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e153
             have i₂ := b3e110
             grind)
          | exact superpose b3e110 b3e153
          | exact resolve b3e153 b3e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e110 b3e153
        have b3e188 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e47 X0 x X1 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e47
          | exact resolve b3e47 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e232 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x x
             have i₂ := b3e188 X0 x
             grind)
          | exact superpose b3e188 b3e12
          | exact resolve b3e12 b3e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e188
        have b3e3009 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e80 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e80
          | exact resolve b3e80 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3010 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e80 y y
             have i₂ := b3e157
             grind)
          | exact superpose b3e157 b3e80
          | (have j0 := b3e80 x y
             grind)
          | exact resolve b3e80 b3e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80 b3e157
        have b3e3147 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b3e3010
        have b3e3148 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e3009
        have b3e3173 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have r₁ := b3e3147
             have r₂ := b3e24
             grind)
          | exact resolve b3e3147 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3147
        have b3e3189 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e3173
             grind)
          | exact superpose b3e3173 b3e24
          | exact resolve b3e24 b3e3173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e3332 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e3148
             grind)
          | exact superpose b3e3148 b3e13
          | exact resolve b3e13 b3e3148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3148
        have b3e3349 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e3332
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e3332
          | exact resolve b3e3332 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3332
        have b3e3361 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e3349
             grind)
          | exact superpose b3e3349 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e3349
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3349
        have b3e3362 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e3361
        have b3e3364 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e3362
             have r₂ := b3e20
             grind)
          | exact resolve b3e3362 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3362
        have b3e3825 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e232 x
             have i₂ := b3e3364
             grind)
          | exact superpose b3e3364 b3e232
          | exact resolve b3e232 b3e3364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e232 b3e3364
        have b3e3841 : y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e3825
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e3825
          | exact resolve b3e3825 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3825
        have b3e3846 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e3841
             have r₂ := b3e20
             grind)
          | exact resolve b3e3841 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3841
        have b3e4057 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e3173
             have i₂ := b3e3846
             grind)
          | exact superpose b3e3846 b3e3173
          | exact resolve b3e3173 b3e3846
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3173 b3e3846
        have b3e4075 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e4057
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e4057
          | exact resolve b3e4057 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4057
        have b3e4082 : False := by grind
        exact b3e4082
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X1) := by
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
          have b5e33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b5e35 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X0 (M.op X1 x)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X0 X0)) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op X0 X0) X1
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e13 X0 X1 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 (M.op X1 X2) X3
               have i₂ := b5e13 (M.op X0 X0) X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) X1))) := by
            intro X0 X1
            grind
          have b5e47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e50 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e53 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e50
          have b5e54 : x = (k x y) := by
            first
            | (have r₁ := b5e53
               have r₂ := b5e21
               grind)
            | exact resolve b5e53 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e66 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X2
               have i₂ := b5e18 X2 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b5e72 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e33
            | exact resolve b5e33 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e92 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e39 X0 x X1 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e39
            | exact resolve b5e39 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e95 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e39 X2 X0 X3 (M.op X1 x)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e39
            | exact resolve b5e39 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e116 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X3) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X0 (M.op X1 X3) X4
               have i₂ := b5e39 (M.op X0 X0) X1 X3 X2
               grind)
            | (have i₁ := b5e13 X0 (M.op X1 X3) X4
               have i₂ := b5e39 (M.op X0 X0) X1 X2 X3
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e119 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op (M.op x x) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e92 X1 (M.op X0 x)
               have i₂ := b5e13 x X0 x
               grind)
            | exact superpose b5e13 b5e92
            | exact resolve b5e92 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e180 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op X1 X1) x
               have i₂ := b5e35 X1 x X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e282 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op X0 (M.op X1 X4)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e39 X0 X1 (M.op x x) X4
               have i₂ := b5e36 X1 x x X0
               grind)
            | exact superpose b5e36 b5e39
            | exact resolve b5e39 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e284 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 X0) (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b5e92 X0 (M.op x x)
               have i₂ := b5e36 x x x X0
               grind)
            | exact superpose b5e36 b5e92
            | exact resolve b5e92 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e299 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 X0) y) := by
            intro X0
            first
            | (have i₁ := b5e284 X0
               have i₂ := b5e92 (M.op X0 X0) x
               grind)
            | exact superpose b5e92 b5e284
            | exact resolve b5e284 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e284
          have b5e361 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e41 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
               have i₂ := b5e36 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2 X0
               grind)
            | exact superpose b5e36 b5e41
            | exact resolve b5e41 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e366 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e361 X0 x x
               have i₂ := b5e35 (M.op X0 X0) (M.op x x) X0
               grind)
            | (have i₁ := b5e361 (M.op x x) x x
               have i₂ := b5e35 (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) (M.op x x))) (M.op x x)) x x
               grind)
            | exact superpose b5e35 b5e361
            | exact resolve b5e361 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e361
          have b5e373 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) := by
            intro X0
            first
            | (have i₁ := b5e366 x
               have i₂ := b5e180 x x
               grind)
            | exact superpose b5e180 b5e366
            | exact resolve b5e366 b5e180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180 b5e366
          have b5e783 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op x x) y) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40 x X0 X1 X2
               have i₂ := b5e92 (M.op x x) x
               grind)
            | exact superpose b5e92 b5e40
            | exact resolve b5e40 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e92
          have b5e923 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op X0 X1) X2)) = (M.op (M.op x y) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e783 X0 X1 X2
               have i₂ := b5e299 x
               grind)
            | exact superpose b5e299 b5e783
            | exact resolve b5e783 b5e299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e783
          have b5e1006 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op x (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e923 X0 X1 X2
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e923
            | exact resolve b5e923 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e923
          have b5e1229 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e69 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e1230 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1229
               have r₂ := b5e24
               grind)
            | exact resolve b5e1229 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1229
          have b5e1231 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1230
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1230
            | exact resolve b5e1230 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1230
          have b5e1232 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1231
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e1231
            | exact resolve b5e1231 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e1231
          have b5e1234 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 (σ x) (σ y)
               have i₂ := b5e1232
               grind)
            | exact superpose b5e1232 b5e13
            | exact resolve b5e13 b5e1232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1232
          have b5e1513 : ∀ X0 X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X2) = X0 ∨ (M.op X2 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e66 X0 X0 X2
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e66 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b5e18 b5e66
            | (have j0 := b5e66 X1 X1 X2
               have j1 := b5e18 X2 X1
               grind)
            | exact resolve b5e66 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e2222 : ∀ X0 X3 : G, (M.op y x) = (M.op x (M.op (M.op y X0) X3)) := by
            intro X0 X3
            first
            | (have i₁ := b5e1006 x (M.op (M.op X0 x) x) X3
               have i₂ := b5e1006 X0 x x
               grind)
            | exact superpose b5e1006 b5e1006
            | exact resolve b5e1006 b5e1006
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2237 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op x (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1006 X0 X1 (M.op (M.op X2 X2) x)
               have i₂ := b5e35 X2 x (M.op X0 X1)
               grind)
            | exact superpose b5e35 b5e1006
            | exact resolve b5e1006 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e2257 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b5e119 x x
               have i₂ := b5e1006 x x x
               grind)
            | exact superpose b5e1006 b5e119
            | exact resolve b5e119 b5e1006
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e119
          have b5e2289 : y = (M.op y x) := by
            first
            | (have i₁ := b5e2257
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2257
            | exact resolve b5e2257 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2257
          have b5e2297 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e2237 X0 X1 x
               have i₂ := b5e1006 (M.op X0 X1) (M.op X0 X1) x
               grind)
            | exact superpose b5e1006 b5e2237
            | exact resolve b5e2237 b5e1006
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2237
          have b5e2304 : (M.op y y) = (M.op y x) := by
            first
            | (have i₁ := b5e2222 x x
               have i₂ := b5e1006 y x x
               grind)
            | exact superpose b5e1006 b5e2222
            | exact resolve b5e2222 b5e1006
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2222
          have b5e2334 : y = (M.op y y) := by
            first
            | (have i₁ := b5e2304
               have i₂ := b5e2289
               grind)
            | exact superpose b5e2289 b5e2304
            | exact resolve b5e2304 b5e2289
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2304
          have b5e2617 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 X2)) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X0) X1 X2
               have i₂ := b5e60 X0 X0
               grind)
            | exact superpose b5e60 b5e13
            | (have j1 := b5e60 X0 X0
               grind)
            | exact resolve b5e13 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2689 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e60 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e2691 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e2689 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2689
          have b5e2708 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 X2)) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e2617 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2617
          have b5e3026 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e1006 X0 X0 x
               have i₂ := b5e95 X0 x x X1
               grind)
            | exact superpose b5e95 b5e1006
            | exact resolve b5e1006 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95 b5e1006
          have b5e7180 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X0 (M.op X1 X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e282 X0 X1 X4
               have i₂ := b5e116 X0 X1 X1 X2 X3
               grind)
            | exact superpose b5e116 b5e282
            | exact resolve b5e282 b5e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e282
          have b5e7182 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X0 (M.op X1 (M.op X4 X5))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e36 X1 X4 X5 X0
               have i₂ := b5e116 X0 X1 X1 X2 X3
               grind)
            | exact superpose b5e116 b5e36
            | exact resolve b5e36 b5e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e116
          have b5e21274 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e2691 (τ X0)
               have i₂ := b5e28 X0 (τ X0)
               grind)
            | exact superpose b5e28 b5e2691
            | (have j0 := b5e2691 (τ X0)
               grind)
            | exact resolve b5e2691 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2691
          have b5e21278 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e21274 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e21274
            | (have j0 := b5e21274 X0
               grind)
            | exact resolve b5e21274 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21274
          have b5e21282 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e21278 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e21278
            | (have j0 := b5e21278 X0
               grind)
            | exact resolve b5e21278 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21278
          have b5e24349 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e21282 (τ X0)
               have i₂ := b5e72 X0 X0
               grind)
            | exact superpose b5e72 b5e21282
            | (have j0 := b5e21282 (τ X0)
               grind)
            | exact resolve b5e21282 b5e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72 b5e21282
          have b5e177517 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op X1 X2)) = (M.op (k (σ (τ X0)) X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e2708 (τ X0) X1 X2
               have i₂ := b5e28 X0 (τ X0)
               grind)
            | exact superpose b5e28 b5e2708
            | (have j0 := b5e2708 (τ X0) X1 X2
               grind)
            | exact resolve b5e2708 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e2708
          have b5e178508 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (k X0 X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e177517 X0 X1 X2
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e177517
            | (have j0 := b5e177517 X0 X1 X2
               grind)
            | exact resolve b5e177517 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e177517
          have b5e178751 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e178508 X0 X1 X2
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e178508
            | (have j0 := b5e178508 X0 X1 X2
               grind)
            | exact resolve b5e178508 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e178508
          have b5e236493 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) ≠ (τ (M.op (M.op X0 X0) X0)) ∨ (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
            intro X0
            first
            | (have i₁ := b5e24349 (M.op (M.op X0 X0) X0)
               have i₂ := b5e373 X0
               grind)
            | exact superpose b5e373 b5e24349
            | (have j0 := b5e24349 (M.op (M.op X0 X0) X0)
               grind)
            | exact resolve b5e24349 b5e373
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e373 b5e24349
          have b5e236506 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
            intro X0
            first
            | (have j0 := b5e236493 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e236493
          have b5e302421 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e7182 X0 X1 X2 X3 x x
               have i₂ := b5e178751 X0 X1 (M.op x x)
               grind)
            | exact superpose b5e178751 b5e7182
            | (have j1 := b5e178751 X0 X1 X2
               grind)
            | exact resolve b5e7182 b5e178751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7182
          have b5e302705 : ∀ X0 : G, (M.op y X0) = (M.op (k x x) X0) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b5e3026 X0 x
               have i₂ := b5e178751 x X0 x
               grind)
            | exact superpose b5e178751 b5e3026
            | (have j1 := b5e178751 x x x
               grind)
            | exact resolve b5e3026 b5e178751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e312381 : (M.op (k x x) y) = (M.op (M.op y (k x x)) y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e299 (k x x)
               have i₂ := b5e302705 (k x x)
               grind)
            | exact superpose b5e302705 b5e299
            | exact resolve b5e299 b5e302705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e299
          have b5e312576 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op X0 X1)) = (M.op (k x x) (M.op (M.op X0 X2) X3)) ∨ x = (M.op x x) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e7180 (k x x) X0 X2 X3 X1
               have i₂ := b5e302705 (M.op X0 X1)
               grind)
            | exact superpose b5e302705 b5e7180
            | exact resolve b5e7180 b5e302705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7180 b5e302705
          have b5e312742 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (k x x) (M.op (M.op X0 X2) X3)) ∨ x = (M.op x x) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e312576 X0 x X2 X3
               have i₂ := b5e2297 X0 x
               grind)
            | exact superpose b5e2297 b5e312576
            | exact resolve b5e312576 b5e2297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2297 b5e312576
          have b5e419950 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e1513 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1513
          have b5e419951 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e419950 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e419950
          have b5e419952 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e419951 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e419951
          have b5e420012 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e47 X0 (σ X0)
               have i₂ := b5e419952 (σ X0)
               grind)
            | exact superpose b5e419952 b5e47
            | (have j1 := b5e419952 (σ X0)
               grind)
            | exact resolve b5e47 b5e419952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e419952
          have b5e420078 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e420012 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e420012
            | (have j0 := b5e420012 X0
               grind)
            | exact resolve b5e420012 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e420012
          have b5e692360 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X1) = (M.op (k X0 X0) (M.op X1 X2)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e178751 X0 (M.op X1 X2) x
               have i₂ := b5e302421 X0 X1 X2 x
               grind)
            | exact superpose b5e302421 b5e178751
            | (have j0 := b5e178751 X0 X1 X2
               have j1 := b5e302421 X0 X1 X2 x
               grind)
            | exact resolve b5e178751 b5e302421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e178751 b5e302421
          have b5e692609 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X1) = (M.op (k X0 X0) (M.op X1 X2)) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e692360 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e692360
          have b5e846764 : (M.op y y) = (M.op (k x x) (M.op (k x x) y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e312742 y (k x x) y
               have i₂ := b5e312381
               grind)
            | exact superpose b5e312381 b5e312742
            | exact resolve b5e312742 b5e312381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e312381 b5e312742
          have b5e847132 : (M.op y y) = (M.op (k x x) (M.op (k x x) y)) ∨ x = (M.op x x) := by grind
          clear b5e846764
          have b5e847358 : y = (M.op (k x x) (M.op (k x x) y)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e847132
               have i₂ := b5e2334
               grind)
            | exact superpose b5e2334 b5e847132
            | exact resolve b5e847132 b5e2334
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2334 b5e847132
          have b5e849779 : y = (M.op (k x x) (k x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e692609 x (k x x) y
               have i₂ := b5e847358
               grind)
            | exact superpose b5e847358 b5e692609
            | (have j0 := b5e692609 x x x
               grind)
            | exact resolve b5e692609 b5e847358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e692609 b5e847358
          have b5e849994 : y = (M.op (k x x) (k x x)) ∨ x = (M.op x x) := by grind
          clear b5e849779
          have b5e1097304 : (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) := by
            first
            | (have i₁ := b5e236506 (σ x)
               have i₂ := b5e1234 (σ x)
               grind)
            | exact superpose b5e1234 b5e236506
            | exact resolve b5e236506 b5e1234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1234 b5e236506
          have b5e1140140 : (k x x) = (M.op (k x x) (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e1097304
               have i₂ := b5e420078 x
               grind)
            | exact superpose b5e420078 b5e1097304
            | (have j1 := b5e420078 x
               grind)
            | exact resolve b5e1097304 b5e420078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e420078
          have b5e1140265 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (k x x) := by
            first
            | (have i₁ := b5e849994
               have i₂ := b5e1140140
               grind)
            | exact superpose b5e1140140 b5e849994
            | exact resolve b5e849994 b5e1140140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e849994 b5e1140140
          have b5e1140321 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) ∨ y = (k x x) := by
            first
            | (have i₁ := b5e1097304
               have i₂ := b5e1140265
               grind)
            | exact superpose b5e1140265 b5e1097304
            | exact resolve b5e1097304 b5e1140265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1097304 b5e1140265
          have b5e1140375 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (k x x) := by
            first
            | (have i₁ := b5e1140321
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e1140321
            | exact resolve b5e1140321 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1140321
          have b5e1140376 : y = (k x x) ∨ x = (M.op x x) := by grind
          clear b5e1140375
          have b5e1140845 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e1140376
               grind)
            | exact superpose b5e1140376 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e1140376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1140376
          have b5e1140868 : y = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b5e1140845
          have b5e1141189 : x = (M.op x x) := by
            first
            | (have r₁ := b5e1140868
               have r₂ := b5e21
               grind)
            | exact resolve b5e1140868 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1140868
          have b5e1141948 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b5e3026 x x
               have i₂ := b5e1141189
               grind)
            | exact superpose b5e1141189 b5e3026
            | exact resolve b5e3026 b5e1141189
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3026 b5e1141189
          have b5e1142462 : y = (M.op x x) := by
            first
            | (have i₁ := b5e1141948
               have i₂ := b5e2289
               grind)
            | exact superpose b5e2289 b5e1141948
            | exact resolve b5e1141948 b5e2289
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2289 b5e1141948
          have b5e1142668 : False := by grind
          exact b5e1142668
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
        have b6e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e79 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
        have b6e90 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e79
             have r₂ := b6e20
             grind)
          | exact resolve b6e79 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e94 : x = (M.op x y) := by
          first
          | (have r₁ := b6e90
             have r₂ := b6e21
             grind)
          | exact resolve b6e90 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e96 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e94
             grind)
          | exact superpose b6e94 b6e21
          | exact resolve b6e21 b6e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e94
        have b6e2801 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
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
        have b6e2938 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e2801
        have b6e3151 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e2938
             grind)
          | exact superpose b6e2938 b6e13
          | exact resolve b6e13 b6e2938
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3168 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3151
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e3151
          | exact resolve b6e3151 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3151
        have b6e3176 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e3168
             grind)
          | exact superpose b6e3168 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e3168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3168
        have b6e3177 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3176
        have b6e3179 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3177
             have r₂ := b6e20
             grind)
          | exact resolve b6e3177 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3177
        have b6e3620 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3179
        have b6e3843 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2938
             have i₂ := b6e3620
             grind)
          | exact superpose b6e3620 b6e2938
          | exact resolve b6e2938 b6e3620
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2938 b6e3620
        have b6e3850 : (σ x) = (σ y) := by grind
        clear b6e3843
        have b6e4310 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e3850
             grind)
          | exact superpose b6e3850 b6e13
          | exact resolve b6e13 b6e3850
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3850
        have b6e4326 : x = y := by
          first
          | (have i₁ := b6e4310
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e4310
          | exact resolve b6e4310 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4310
        have b6e4332 : False := by grind
        exact b6e4332
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X1) := by
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
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b7e29 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op X0 (σ y)) := by
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
          have b7e30 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X0 (M.op X1 x)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X0 X0)) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op X0 X0) X1
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X2 X3)) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X0 X0) X2 X3
               have i₂ := b7e13 X0 (M.op X0 X0) X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e13 X0 X1 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 (M.op X1 X2) X3
               have i₂ := b7e13 (M.op X0 X0) X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) X1))) := by
            intro X0 X1
            grind
          have b7e41 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e47 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e48 : (σ x) = (σ (k x y)) := by
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
          have b7e51 : (k x y) = (τ (σ x)) := by
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
          have b7e52 : x = (k x y) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e51
            | exact resolve b7e51 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e62 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e73 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
          have b7e74 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e73
               have r₂ := b7e21
               grind)
            | exact resolve b7e73 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e76 : x = (M.op x y) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e22
               grind)
            | exact resolve b7e74 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e87 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e76
               grind)
            | exact superpose b7e76 b7e26
            | exact resolve b7e26 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e88 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e76
               grind)
            | exact superpose b7e76 b7e22
            | exact resolve b7e22 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e93 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ x) X1
               have i₂ := b7e29 X0
               grind)
            | exact superpose b7e29 b7e13
            | exact resolve b7e13 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e95 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op X1 (M.op X0 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (M.op X0 X0) (σ x)
               have i₂ := b7e29 X0
               grind)
            | exact superpose b7e29 b7e13
            | exact resolve b7e13 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e113 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e34 X2 X0 X3 (M.op X1 x)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e34
            | exact resolve b7e34 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e116 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op (M.op X0 X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e34 X1 (M.op X0 X0) X2 (σ x)
               have i₂ := b7e29 X0
               grind)
            | exact superpose b7e29 b7e34
            | exact resolve b7e34 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e118 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X0 x X1 y
               have i₂ := b7e76
               grind)
            | exact superpose b7e76 b7e34
            | exact resolve b7e34 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e152 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) ∨ (M.op X1 (M.op X0 X2)) = X0 ∨ (M.op (M.op X1 X1) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e30 (M.op X2 X2) X1 X2
               have i₂ := b7e18 (M.op X2 X2) X1
               grind)
            | (have i₁ := b7e30 X0 X1 X2
               have i₂ := b7e18 X0 (M.op (M.op X2 X2) X0)
               grind)
            | exact superpose b7e18 b7e30
            | (have j1 := b7e18 (M.op X1 X1) X0
               grind)
            | exact resolve b7e30 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e182 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (M.op X1 X1) x
               have i₂ := b7e30 X1 x X0
               grind)
            | exact superpose b7e30 b7e13
            | exact resolve b7e13 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e279 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op X0 (M.op X1 X4)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e34 X0 X1 (M.op x x) X4
               have i₂ := b7e31 X1 x x X0
               grind)
            | exact superpose b7e31 b7e34
            | exact resolve b7e34 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e281 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e30 X1 (M.op x x) X0
               have i₂ := b7e31 (M.op X1 X1) x x X0
               grind)
            | exact superpose b7e31 b7e30
            | exact resolve b7e30 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e293 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X1 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e281 X0 X1
               have i₂ := b7e116 X1 (M.op X0 X0) (M.op X1 X1)
               grind)
            | exact superpose b7e116 b7e281
            | exact resolve b7e281 b7e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e281
          have b7e327 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x x
               have i₂ := b7e118 X0 x
               grind)
            | exact superpose b7e118 b7e13
            | exact resolve b7e13 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118
          have b7e373 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
            intro X0
            first
            | (have i₁ := b7e36 X0 x
               have i₂ := b7e30 X0 x X0
               grind)
            | exact superpose b7e30 b7e36
            | exact resolve b7e36 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e426 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op (M.op X3 X3) X5)) (M.op X0 (M.op (M.op X0 X0) X4))) = (M.op (M.op X3 X3) (M.op (M.op X0 X0) (M.op X1 X2))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e33 X3 X5 (M.op X0 (M.op (M.op X0 X0) X4)) X1
               have i₂ := b7e33 X0 X4 X1 X2
               grind)
            | exact superpose b7e33 b7e33
            | exact resolve b7e33 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e449 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (M.op X0 (M.op X0 x)) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e33 X0 x X1 X2
               have i₂ := b7e327 X0
               grind)
            | exact superpose b7e327 b7e33
            | exact resolve b7e33 b7e327
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e482 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X2) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op X0 X0) X2 x
               have i₂ := b7e33 X0 X1 X2 x
               grind)
            | exact superpose b7e33 b7e13
            | exact resolve b7e13 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e543 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X2) = (M.op (M.op (M.op X0 X0) X0) X2) := by
            intro X0 X2
            first
            | (have i₁ := b7e482 X0 x X2
               have i₂ := b7e30 X0 x X0
               grind)
            | (have i₁ := b7e482 (M.op X2 X2) x X2
               have i₂ := b7e30 (M.op (M.op (M.op X2 X2) (M.op X2 X2)) x) x X2
               grind)
            | exact superpose b7e30 b7e482
            | exact resolve b7e482 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e482
          have b7e577 : ∀ X0 X3 X4 X5 : G, (M.op (M.op X3 (M.op (M.op X3 X3) X5)) (M.op X0 (M.op (M.op X0 X0) X4))) = (M.op (M.op X3 X3) (M.op X0 (σ y))) := by
            intro X0 X3 X4 X5
            first
            | (have i₁ := b7e426 X0 x x X3 X4 X5
               have i₂ := b7e116 X0 (M.op X3 X3) (M.op x x)
               grind)
            | exact superpose b7e116 b7e426
            | exact resolve b7e426 b7e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e426
          have b7e605 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) X0) X2) = (M.op (M.op X0 (M.op X0 (σ y))) X2) := by
            intro X0 X2
            first
            | (have i₁ := b7e543 X0 X2
               have i₂ := b7e95 X0 X0
               grind)
            | exact superpose b7e95 b7e543
            | exact resolve b7e543 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e543
          have b7e625 : ∀ X0 X3 X4 X5 : G, (M.op (M.op X3 X3) X0) = (M.op (M.op X3 (M.op (M.op X3 X3) X5)) (M.op X0 (M.op (M.op X0 X0) X4))) := by
            intro X0 X3 X4 X5
            first
            | (have i₁ := b7e577 X0 X3 X4 X5
               have i₂ := b7e293 X3 X0
               grind)
            | exact superpose b7e293 b7e577
            | exact resolve b7e577 b7e293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e293 b7e577
          have b7e642 : ∀ X0 X3 X5 : G, (M.op (M.op X3 X3) X0) = (M.op (M.op X3 (M.op (M.op X3 X3) X5)) (M.op (M.op X0 X0) X0)) := by
            intro X0 X3 X5
            first
            | (have i₁ := b7e625 X0 X3 x X5
               have i₂ := b7e30 X0 x X0
               grind)
            | (have i₁ := b7e625 (M.op x x) X3 x X5
               have i₂ := b7e30 (M.op (M.op (M.op x x) (M.op x x)) x) x x
               grind)
            | exact superpose b7e30 b7e625
            | exact resolve b7e625 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e625
          have b7e652 : ∀ X0 X3 X5 : G, (M.op (M.op X3 X3) X0) = (M.op (M.op X3 (M.op (M.op X3 X3) X5)) (M.op X0 (σ y))) := by
            intro X0 X3 X5
            first
            | (have i₁ := b7e642 X0 X3 X5
               have i₂ := b7e116 X0 (M.op X3 (M.op (M.op X3 X3) X5)) X0
               grind)
            | exact superpose b7e116 b7e642
            | exact resolve b7e642 b7e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e642
          have b7e660 : ∀ X0 X3 : G, (M.op (M.op X3 X3) X0) = (M.op (M.op (M.op X3 X3) X3) (M.op X0 (σ y))) := by
            intro X0 X3
            first
            | (have i₁ := b7e652 X0 X3 x
               have i₂ := b7e30 X3 x X3
               grind)
            | (have i₁ := b7e652 X0 (M.op x x) x
               have i₂ := b7e30 (M.op (M.op (M.op x x) (M.op x x)) x) x x
               grind)
            | exact superpose b7e30 b7e652
            | exact resolve b7e652 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e652
          have b7e706 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e35 X1 X0 X0 x
               have i₂ := b7e327 X0
               grind)
            | exact superpose b7e327 b7e35
            | exact resolve b7e35 b7e327
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e761 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e30 X1 x X0
               have i₂ := b7e35 X0 X1 X1 x
               grind)
            | exact superpose b7e35 b7e30
            | exact resolve b7e30 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e788 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X5)) X1) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e33 (M.op X0 X0) X5 X1 X2
               have i₂ := b7e35 X0 (M.op X1 X2) X3 X4
               grind)
            | exact superpose b7e35 b7e33
            | exact resolve b7e33 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e805 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op (M.op X4 X4) X5)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X4 X4) (M.op X0 (M.op (M.op X1 X2) X3))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e33 X4 X5 (M.op (M.op X0 X0) (M.op X0 X0)) X1
               have i₂ := b7e35 X0 X1 X2 X3
               grind)
            | exact superpose b7e35 b7e33
            | exact resolve b7e33 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e35
          have b7e828 : ∀ X0 X4 X5 : G, (M.op (M.op X4 (M.op X4 x)) X0) = (M.op (M.op X4 (M.op (M.op X4 X4) X5)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0 X4 X5
            first
            | (have i₁ := b7e805 X0 x x x X4 X5
               have i₂ := b7e449 X4 X0 (M.op (M.op x x) x)
               grind)
            | exact superpose b7e449 b7e805
            | exact resolve b7e805 b7e449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e449 b7e805
          have b7e842 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) X1) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e788 X0 X1 X2 X3 X4 x
               have i₂ := b7e30 (M.op X0 X0) x (M.op X0 X0)
               grind)
            | (have i₁ := b7e788 X2 X1 X2 X3 X4 x
               have i₂ := b7e30 (M.op (M.op (M.op X2 X2) (M.op X2 X2)) x) X1 X2
               grind)
            | exact superpose b7e30 b7e788
            | exact resolve b7e788 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e788
          have b7e862 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 (M.op X0 (σ y))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e761 X0 X1
               have i₂ := b7e95 X0 X0
               grind)
            | exact superpose b7e95 b7e761
            | exact resolve b7e761 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e761
          have b7e896 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op (M.op X1 (M.op X1 (σ y))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e706 X0 X1
               have i₂ := b7e95 X1 X1
               grind)
            | exact superpose b7e95 b7e706
            | exact resolve b7e706 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e706
          have b7e923 : ∀ X0 X4 X5 : G, (M.op (M.op X4 (M.op X4 x)) X0) = (M.op (M.op X4 (M.op (M.op X4 X4) X5)) (M.op X0 (σ y))) := by
            intro X0 X4 X5
            first
            | (have i₁ := b7e828 X0 X4 X5
               have i₂ := b7e116 X0 (M.op X4 (M.op (M.op X4 X4) X5)) (M.op X0 X0)
               grind)
            | exact superpose b7e116 b7e828
            | exact resolve b7e828 b7e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116 b7e828
          have b7e936 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (σ y))) X1) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e842 X0 X1 X2 X3 X4
               have i₂ := b7e605 (M.op X0 X0) X1
               grind)
            | exact superpose b7e605 b7e842
            | exact resolve b7e842 b7e605
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e605 b7e842
          have b7e981 : ∀ X0 X4 : G, (M.op (M.op X4 (M.op X4 x)) X0) = (M.op (M.op (M.op X4 X4) X4) (M.op X0 (σ y))) := by
            intro X0 X4
            first
            | (have i₁ := b7e923 X0 X4 x
               have i₂ := b7e30 X4 x X4
               grind)
            | (have i₁ := b7e923 X0 (M.op x x) x
               have i₂ := b7e30 (M.op (M.op (M.op x x) (M.op x x)) x) x x
               grind)
            | exact superpose b7e30 b7e923
            | exact resolve b7e923 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e923
          have b7e994 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e936 X0 X1 X2 X3 X4
               have i₂ := b7e862 (M.op X0 X0) X1
               grind)
            | exact superpose b7e862 b7e936
            | exact resolve b7e936 b7e862
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e862 b7e936
          have b7e1027 : ∀ X0 X4 : G, (M.op (M.op X4 X4) X0) = (M.op (M.op X4 (M.op X4 x)) X0) := by
            intro X0 X4
            first
            | (have i₁ := b7e981 X0 X4
               have i₂ := b7e660 X0 X4
               grind)
            | exact superpose b7e660 b7e981
            | exact resolve b7e981 b7e660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e660 b7e981
          have b7e1036 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 (σ y))) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e994 X0 X1 X2 X3 X4
               have i₂ := b7e95 X0 X0
               grind)
            | exact superpose b7e95 b7e994
            | exact resolve b7e994 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95 b7e994
          have b7e1067 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) = (M.op X0 (M.op X1 x)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e1036 X0 X1 X2 X3 X4
               have i₂ := b7e896 X1 X0
               grind)
            | exact superpose b7e896 b7e1036
            | exact resolve b7e1036 b7e896
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e896 b7e1036
          have b7e1127 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e62 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e1763 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (σ y)) = (M.op X0 (M.op (σ x) (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e31 (σ x) X1 X2 X0
               have i₂ := b7e93 (M.op X0 X0) (σ x)
               grind)
            | exact superpose b7e93 b7e31
            | exact resolve b7e31 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e1780 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e1763 X0 x x
               have i₂ := b7e93 X0 (M.op x x)
               grind)
            | exact superpose b7e93 b7e1763
            | exact resolve b7e1763 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1763
          have b7e1931 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ y) X1
               have i₂ := b7e1780 X0
               grind)
            | exact superpose b7e1780 b7e13
            | exact resolve b7e13 b7e1780
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2646 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e58 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2648 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e2646 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2646
          have b7e2862 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X4)) = (M.op X3 (M.op (M.op X0 X1) X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e113 (M.op X0 X1) X4 X3 X5
               have i₂ := b7e34 (M.op X0 X1) X0 X1 X2
               grind)
            | (have i₁ := b7e113 (M.op X0 X1) X4 X3 X5
               have i₂ := b7e34 (M.op X0 X1) X0 X2 X1
               grind)
            | exact superpose b7e34 b7e113
            | exact resolve b7e113 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3195 : ∀ X0 X1 X3 X5 : G, (M.op X3 (M.op X0 x)) = (M.op X3 (M.op (M.op X0 X1) X5)) := by
            intro X0 X1 X3 X5
            first
            | (have i₁ := b7e2862 X0 X1 x X3 x X5
               have i₂ := b7e1067 X3 X0 X1 (M.op X0 x) x
               grind)
            | exact superpose b7e1067 b7e2862
            | exact resolve b7e2862 b7e1067
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1067 b7e2862
          have b7e3585 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e34 (M.op X0 X0) X1 X3 X1
               have i₂ := b7e279 X0 X1 X2
               grind)
            | exact superpose b7e279 b7e34
            | exact resolve b7e34 b7e279
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e3891 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b7e373 (σ x)
               have i₂ := b7e29 (σ x)
               grind)
            | exact superpose b7e29 b7e373
            | exact resolve b7e373 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3893 : (M.op x x) = (k (M.op x x) (M.op x x)) := by
            first
            | (have i₁ := b7e373 x
               have i₂ := b7e327 x
               grind)
            | exact superpose b7e327 b7e373
            | exact resolve b7e373 b7e327
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e327 b7e373
          have b7e3926 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e3891
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e3891
            | exact resolve b7e3891 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3891
          have b7e4000 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b7e1027 X0 (σ x)
               have i₂ := b7e93 (σ x) x
               grind)
            | exact superpose b7e93 b7e1027
            | exact resolve b7e1027 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93 b7e1027
          have b7e4153 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e4000 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e4000
            | exact resolve b7e4000 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4000
          have b7e4363 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e279 (σ x) X0 X1
               have i₂ := b7e4153 (M.op X0 X0)
               grind)
            | exact superpose b7e4153 b7e279
            | exact resolve b7e279 b7e4153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e4364 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e182 (σ x) X0
               have i₂ := b7e4153 (M.op X0 X0)
               grind)
            | exact superpose b7e4153 b7e182
            | exact resolve b7e182 b7e4153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e182
          have b7e4368 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e29 (σ x)
               have i₂ := b7e4153 (σ x)
               grind)
            | exact superpose b7e4153 b7e29
            | exact resolve b7e29 b7e4153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e4382 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ x))) = (k (M.op (σ y) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ y) (M.op (σ x) (σ x))) X0))) := by
            intro X0
            first
            | (have i₁ := b7e36 (M.op (σ x) (σ x)) x
               have i₂ := b7e4153 (M.op (σ x) (σ x))
               grind)
            | exact superpose b7e4153 b7e36
            | exact resolve b7e36 b7e4153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e4481 : (M.op (σ y) (M.op (σ x) (σ x))) = (k (M.op (σ y) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ x)) (M.op (σ y) x))) := by
            first
            | (have i₁ := b7e4382 x
               have i₂ := b7e3195 (σ y) (M.op (σ x) (σ x)) (M.op (σ x) (σ x)) x
               grind)
            | exact superpose b7e3195 b7e4382
            | exact resolve b7e4382 b7e3195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3195 b7e4382
          have b7e4494 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e4368
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e4368
            | exact resolve b7e4368 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4368
          have b7e4498 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e4364 X0
               have i₂ := b7e4153 X0
               grind)
            | exact superpose b7e4153 b7e4364
            | exact resolve b7e4364 b7e4153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4153 b7e4364
          have b7e4558 : (M.op (σ y) (M.op (σ x) (σ x))) = (k (M.op (σ y) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ x)) (σ y))) := by
            first
            | (have i₁ := b7e4481
               have i₂ := b7e1931 (M.op (σ x) (σ x)) x
               grind)
            | exact superpose b7e1931 b7e4481
            | exact resolve b7e4481 b7e1931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1931 b7e4481
          have b7e4610 : (M.op (σ y) (M.op (σ x) (σ x))) = (k (M.op (σ y) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b7e4558
               have i₂ := b7e1780 (σ x)
               grind)
            | exact superpose b7e1780 b7e4558
            | exact resolve b7e4558 b7e1780
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1780 b7e4558
          have b7e4644 : (M.op (σ y) (M.op (σ x) (σ x))) = (k (M.op (σ y) (M.op (σ x) (σ x))) (σ y)) := by
            first
            | (have i₁ := b7e4610
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e4610
            | exact resolve b7e4610 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4610
          have b7e4660 : (M.op (σ y) (σ x)) = (k (M.op (σ y) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e4644
               have i₂ := b7e4498 (σ x)
               grind)
            | exact superpose b7e4498 b7e4644
            | exact resolve b7e4644 b7e4498
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4498 b7e4644
          have b7e4670 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e4660
               have i₂ := b7e4494
               grind)
            | exact superpose b7e4494 b7e4660
            | exact resolve b7e4660 b7e4494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4660
          have b7e4679 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e4670
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e4670
            | exact resolve b7e4670 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4670
          have b7e4955 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e4679
               grind)
            | exact superpose b7e4679 b7e14
            | exact resolve b7e14 b7e4679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4679
          have b7e4972 : y = (k y y) := by
            first
            | (have i₁ := b7e4955
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e4955
            | exact resolve b7e4955 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4955
          have b7e5264 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e4972
               grind)
            | exact superpose b7e4972 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e4972
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4972
          have b7e5265 : y = (M.op y y) := by grind
          clear b7e5264
          have b7e5497 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b7e113 y X1 x y
               have i₂ := b7e5265
               grind)
            | exact superpose b7e5265 b7e113
            | exact resolve b7e113 b7e5265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113
          have b7e5498 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 X0) y) := by
            intro X0
            first
            | (have i₁ := b7e279 X0 y y
               have i₂ := b7e5265
               grind)
            | exact superpose b7e5265 b7e279
            | exact resolve b7e279 b7e5265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e279 b7e5265
          have b7e20919 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e1127 (σ y) (σ x)
               have i₂ := b7e4494
               grind)
            | exact superpose b7e4494 b7e1127
            | (have j0 := b7e1127 (σ y) (σ x)
               grind)
            | (have r₁ := b7e1127 (σ y) (σ x)
               have r₂ := b7e4494
               grind)
            | exact resolve b7e1127 b7e4494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1127
          have b7e20927 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b7e20919
          have b7e20928 : (σ y) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b7e20927
               have r₂ := b7e87
               grind)
            | exact resolve b7e20927 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87 b7e20927
          have b7e20954 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e20928
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e20928
            | exact resolve b7e20928 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20928
          have b7e20996 : (τ (σ y)) = (k y x) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e20954
               grind)
            | exact superpose b7e20954 b7e14
            | exact resolve b7e14 b7e20954
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e20998 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (k y x))) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 (k y x)
               have i₂ := b7e20954
               grind)
            | exact superpose b7e20954 b7e19
            | exact resolve b7e19 b7e20954
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20954
          have b7e21026 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (k y x))) := by
            intro X0
            first
            | (have i₁ := b7e20998 X0
               have i₂ := b7e19 X0 y
               grind)
            | exact superpose b7e19 b7e20998
            | exact resolve b7e20998 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20998
          have b7e21028 : y = (k y x) := by
            first
            | (have i₁ := b7e20996
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e20996
            | exact resolve b7e20996 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20996
          have b7e21041 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e2648 (M.op x x)
               have i₂ := b7e3893
               grind)
            | exact superpose b7e3893 b7e2648
            | (have j0 := b7e2648 (M.op x x)
               grind)
            | exact resolve b7e2648 b7e3893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2648 b7e3893
          have b7e21053 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by grind
          clear b7e21041
          have b7e123340 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) y) := by
            first
            | (have i₁ := b7e41 (M.op (σ x) (σ x)) y
               have i₂ := b7e3926
               grind)
            | exact superpose b7e3926 b7e41
            | exact resolve b7e41 b7e3926
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41 b7e3926
          have b7e136981 : (M.op (σ y) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e4363 (σ (M.op x x)) (σ (M.op x x))
               have i₂ := b7e21053
               grind)
            | exact superpose b7e21053 b7e4363
            | exact resolve b7e4363 b7e21053
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21053
          have b7e199958 : (τ (σ (k x x))) = (k (τ (σ (k x x))) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e123340
               have i₂ := b7e58 x x
               grind)
            | exact superpose b7e58 b7e123340
            | (have j1 := b7e58 x x
               grind)
            | exact resolve b7e123340 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58 b7e123340
          have b7e199969 : (τ (σ (k x x))) = (k (τ (σ (k x x))) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b7e199958
          have b7e199972 : (k x x) = (k (k x x) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e199969
               have i₂ := b7e14 (k x x)
               grind)
            | exact superpose b7e14 b7e199969
            | exact resolve b7e199969 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e199969
          have b7e219063 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) y)) = (σ (M.op (M.op X0 X0) (k y x))) ∨ (k y x) = (M.op X0 (M.op (k y x) X1)) ∨ (k y x) = (M.op (M.op X0 X0) (k y x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e21026 (M.op X0 X0)
               have i₂ := b7e152 (k y x) X0 X1
               grind)
            | exact superpose b7e152 b7e21026
            | (have j1 := b7e152 (k y x) X0 X1
               grind)
            | exact resolve b7e21026 b7e152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e152 b7e21026
          have b7e219471 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) y)) = (σ (M.op (M.op X0 X0) y)) ∨ (k y x) = (M.op X0 (M.op (k y x) X1)) ∨ (k y x) = (M.op (M.op X0 X0) (k y x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e219063 X0 X1
               have i₂ := b7e21028
               grind)
            | exact superpose b7e21028 b7e219063
            | (have j0 := b7e219063 X0 X1
               grind)
            | exact resolve b7e219063 b7e21028
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e219063
          have b7e219486 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) y)) = (σ (M.op X0 y)) ∨ (k y x) = (M.op X0 (M.op (k y x) X1)) ∨ (k y x) = (M.op (M.op X0 X0) (k y x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e219471 X0 X1
               have i₂ := b7e5498 X0
               grind)
            | exact superpose b7e5498 b7e219471
            | (have j0 := b7e219471 X0 X1
               grind)
            | exact resolve b7e219471 b7e5498
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e219471
          have b7e219494 : ∀ X0 X1 : G, y = (M.op X0 (M.op y X1)) ∨ (σ (k (M.op X0 X0) y)) = (σ (M.op X0 y)) ∨ (k y x) = (M.op (M.op X0 X0) (k y x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e219486 X0 X1
               have i₂ := b7e21028
               grind)
            | exact superpose b7e21028 b7e219486
            | (have j0 := b7e219486 X0 X1
               grind)
            | exact resolve b7e219486 b7e21028
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e219486
          have b7e219502 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (k (M.op X0 X0) y)) = (σ (M.op X0 y)) ∨ (k y x) = (M.op (M.op X0 X0) (k y x)) := by
            intro X0
            first
            | (have i₁ := b7e219494 X0 x
               have i₂ := b7e5497 X0 x
               grind)
            | exact superpose b7e5497 b7e219494
            | (have j0 := b7e219494 X0 x
               grind)
            | exact resolve b7e219494 b7e5497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5497 b7e219494
          have b7e219510 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) ∨ y = (M.op X0 y) ∨ (σ (k (M.op X0 X0) y)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e219502 X0
               have i₂ := b7e21028
               grind)
            | exact superpose b7e21028 b7e219502
            | (have j0 := b7e219502 X0
               grind)
            | exact resolve b7e219502 b7e21028
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21028 b7e219502
          have b7e219514 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op X0 y) ∨ (σ (k (M.op X0 X0) y)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e219510 X0
               have i₂ := b7e5498 X0
               grind)
            | exact superpose b7e5498 b7e219510
            | (have j0 := b7e219510 X0
               grind)
            | exact resolve b7e219510 b7e5498
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e219510
          have b7e219515 : ∀ X0 : G, (σ (k (M.op X0 X0) y)) = (σ (M.op X0 y)) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b7e219514 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e219514
          have b7e406992 : ∀ X0 : G, (k (M.op X0 X0) y) = (τ (σ (M.op X0 y))) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e14 (k (M.op X0 X0) y)
               have i₂ := b7e219515 X0
               grind)
            | exact superpose b7e219515 b7e14
            | (have j1 := b7e219515 X0
               grind)
            | exact resolve b7e14 b7e219515
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e219515
          have b7e407028 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 X0) y) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e406992 X0
               have i₂ := b7e14 (M.op X0 y)
               grind)
            | exact superpose b7e14 b7e406992
            | (have j0 := b7e406992 X0
               grind)
            | exact resolve b7e406992 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e406992
          have b7e407317 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (k (M.op X0 (M.op X0 X1)) y) ∨ y = (M.op (M.op X0 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b7e407028 (M.op X0 X0)
               have i₂ := b7e3585 X0 X0 X1 X0
               grind)
            | exact superpose b7e3585 b7e407028
            | (have j0 := b7e407028 (M.op X0 X0)
               grind)
            | exact resolve b7e407028 b7e3585
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3585 b7e407028
          have b7e407423 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X0 (M.op X0 X1)) y) ∨ y = (M.op (M.op X0 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b7e407317 X0 X1
               have i₂ := b7e5498 X0
               grind)
            | exact superpose b7e5498 b7e407317
            | (have j0 := b7e407317 X0 X1
               grind)
            | exact resolve b7e407317 b7e5498
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e407317
          have b7e407471 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X0 (M.op X0 X1)) y) ∨ y = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b7e407423 X0 X1
               have i₂ := b7e5498 X0
               grind)
            | exact superpose b7e5498 b7e407423
            | (have j0 := b7e407423 X0 X1
               grind)
            | exact resolve b7e407423 b7e5498
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5498 b7e407423
          have b7e474507 : x = (k (M.op x x) y) ∨ x = y := by
            first
            | (have i₁ := b7e407471 x y
               have i₂ := b7e76
               grind)
            | exact superpose b7e76 b7e407471
            | exact resolve b7e407471 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76 b7e407471
          have b7e474727 : x = (k (M.op x x) y) := by
            first
            | (have r₁ := b7e474507
               have r₂ := b7e88
               grind)
            | exact resolve b7e474507 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88 b7e474507
          have b7e571191 : (M.op x x) = (k (M.op x x) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e199972
               have i₂ := b7e18 x x
               grind)
            | exact superpose b7e18 b7e199972
            | (have j1 := b7e18 (σ x) (σ x)
               grind)
            | exact resolve b7e199972 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e199972
          have b7e571198 : (M.op x x) = (k (M.op x x) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b7e571191
          have b7e571201 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e571198
               have i₂ := b7e474727
               grind)
            | exact superpose b7e474727 b7e571198
            | exact resolve b7e571198 b7e474727
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e474727 b7e571198
          have b7e571202 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b7e571201
          have b7e574743 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e4363 (σ x) (σ x)
               have i₂ := b7e571202
               grind)
            | exact superpose b7e571202 b7e4363
            | exact resolve b7e4363 b7e571202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4363 b7e571202
          have b7e574772 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e574743
               have i₂ := b7e4494
               grind)
            | exact superpose b7e4494 b7e574743
            | exact resolve b7e574743 b7e4494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e574743
          have b7e574863 : x = (M.op x x) := by
            first
            | (have r₁ := b7e574772
               have r₂ := b7e23
               grind)
            | exact resolve b7e574772 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e574772
          have b7e577826 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e136981
               have i₂ := b7e574863
               grind)
            | exact superpose b7e574863 b7e136981
            | exact resolve b7e136981 b7e574863
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e136981 b7e574863
          have b7e578325 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e577826
               have i₂ := b7e4494
               grind)
            | exact superpose b7e4494 b7e577826
            | exact resolve b7e577826 b7e4494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4494 b7e577826
          have b7e578365 : False := by grind
          exact b7e578365
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
          have b8e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b8e1442 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e63 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e1443 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1442
               have r₂ := b8e24
               grind)
            | exact resolve b8e1442 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1442
          have b8e1444 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1443
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1443
            | exact resolve b8e1443 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1443
          have b8e1445 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1444
               grind)
            | exact superpose b8e1444 b8e20
            | exact resolve b8e20 b8e1444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1444
          have b8e2149 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1445
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1445
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1445 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1445
          have b8e2150 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e2149
          have b8e2152 : y = (M.op x y) := by
            first
            | (have r₁ := b8e2150
               have r₂ := b8e21
               grind)
            | exact resolve b8e2150 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2150
          have b8e2154 : False := by grind
          exact b8e2154

/-- `Equation4509`: `x ◇ (y ◇ z) = (x ◇ x) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation4509 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4509 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4509.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
        intro X0 X1 X2 X3
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 (τ X0) X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e17
        | exact resolve b0e17 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
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
      have b0e31 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (σ y) (σ y) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X4) := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e11 X0 x x X4
           have i₂ := b0e11 X0 x x X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op X3 X4)) = (M.op (M.op X0 (M.op X1 X2)) X5) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e11 (M.op X0 X0) X3 X4 X5
           have i₂ := b0e11 X0 X1 X2 (M.op X0 X0)
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 y X0 X1 X2
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X0 X1 X2 x
           have i₂ := b0e11 X0 X3 X4 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 X3 : G, (M.op y X0) = (M.op y X3) := by
        intro X0 X3
        first
        | (have i₁ := b0e36 x x X3
           have i₂ := b0e36 x x X0
           grind)
        | (have i₁ := b0e36 X0 x x
           have i₂ := b0e36 X0 x (M.op X0 x)
           grind)
        | exact superpose b0e36 b0e36
        | exact resolve b0e36 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e58 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 X0) ∨ (M.op X3 X3) = X3 ∨ (M.op (M.op X0 X0) X3) = (k (M.op X0 X0) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e15 (M.op X0 X0) X3
           have i₂ := b0e11 X0 X1 X2 (M.op X0 X0)
           grind)
        | exact superpose b0e11 b0e15
        | (have j0 := b0e15 (M.op X0 X0) X3
           grind)
        | (have r₁ := b0e15 (M.op (M.op X1 X2) (M.op X1 X2)) X1
           have r₂ := b0e11 (M.op X1 X2) X1 X2 (M.op (M.op X1 X2) (M.op X1 X2))
           grind)
        | exact resolve b0e15 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e63 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 X0) ∨ (M.op X0 (σ y)) = (k (M.op X0 X0) X3) ∨ (M.op X3 X3) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e58 X0 X1 X2 X3
           have i₂ := b0e31 X0 X3
           grind)
        | exact superpose b0e31 b0e58
        | (have j0 := b0e58 X0 X1 X2 X3
           grind)
        | exact resolve b0e58 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e85 : ∀ X0 : G, y = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e19
           have i₂ := b0e46 y X0
           grind)
        | (have i₁ := b0e19
           have i₂ := b0e46 X0 y
           grind)
        | exact superpose b0e46 b0e19
        | exact resolve b0e19 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e104 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e16 X2 X0
           grind)
        | exact superpose b0e16 b0e15
        | (have j0 := b0e15 X0 X1
           have j1 := b0e16 X1 X1
           grind)
        | (have r₁ := b0e15 X1 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e15 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e15 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e105 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 X3) ∨ (M.op X4 X4) = X4 ∨ (k X4 X0) = (M.op X0 X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X0 X1 X2 X3
           have i₂ := b0e16 X4 X0
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X4 X4
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e106 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e16 X2 X0
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X1 X0
           have j1 := b0e16 X2 X2
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e109 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op X3 X3) = X3 ∨ (k X3 (M.op X0 X1)) = (M.op (M.op X0 X1) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X1 X2) X1 X2 X3
           have i₂ := b0e16 X0 (M.op X1 X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X3 X3
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e113 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e16 X0 X2
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X1 X0
           have j1 := b0e16 X2 X2
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e116 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op X3 X3) = X3 ∨ (k (M.op X0 X1) X3) = (M.op X3 (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X1 X2) X1 X2 X3
           have i₂ := b0e16 (M.op X1 X2) X1
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X3 X3
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e117 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 X0) ∨ (M.op X3 X3) = X3 ∨ (k (M.op X0 X0) X3) = (M.op X3 (M.op X0 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X1 X2 (M.op X0 X0)
           have i₂ := b0e16 (M.op X0 X0) X3
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X3 X3
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e118 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e16 (σ X1) (σ X0)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X0) (σ X0)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e121 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e113 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113
      have b0e123 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e106 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e106
      have b0e124 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e104 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e104
      have b0e142 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op X0 y) := by
        intro X0 X2
        first
        | (have i₁ := b0e11 X0 y x X2
           have i₂ := b0e85 x
           grind)
        | exact superpose b0e85 b0e11
        | exact resolve b0e11 b0e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85
      have b0e169 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e191 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 X2 x
           have i₂ := b0e31 X0 x
           grind)
        | exact superpose b0e31 b0e11
        | exact resolve b0e11 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e230 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X3 X3) = X3 ∨ (k X0 X3) = (M.op X3 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e32 X0 X1 x
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e32
        | (have j1 := b0e16 X3 X3
           grind)
        | exact resolve b0e32 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e323 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e31 X0 x
           have i₂ := b0e142 X0 x
           grind)
        | exact superpose b0e142 b0e31
        | exact resolve b0e31 b0e142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e324 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 X2 x
           have i₂ := b0e142 X0 x
           grind)
        | exact superpose b0e142 b0e11
        | exact resolve b0e11 b0e142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e330 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (M.op X0 y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e31 (M.op X0 X0) X1
           have i₂ := b0e142 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e142 b0e31
        | exact resolve b0e31 b0e142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e336 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X0 y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e330 X0 X1
           have i₂ := b0e31 X0 (σ y)
           grind)
        | exact superpose b0e31 b0e330
        | exact resolve b0e330 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e330
      have b0e353 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e336 X0 X1
           have i₂ := b0e323 X0
           grind)
        | exact superpose b0e323 b0e336
        | exact resolve b0e336 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e336
      have b0e438 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e323 (σ x)
           grind)
        | exact superpose b0e323 b0e18
        | exact resolve b0e18 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e993 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X3 X4)) ≠ (M.op (M.op X0 X0) (M.op X1 X2)) ∨ (k X5 (M.op X0 (M.op X3 X4))) = X5 := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e14 X5 (M.op X0 (M.op X3 X4))
           have i₂ := b0e34 X0 X3 X4 X1 X2 (M.op X0 (M.op X3 X4))
           grind)
        | (have i₁ := b0e14 X0 (M.op X4 X4)
           have i₂ := b0e34 X4 X1 X2 X4 X4 X5
           grind)
        | exact superpose b0e34 b0e14
        | (have j0 := b0e14 X5 (M.op X0 (M.op X3 X4))
           grind)
        | exact resolve b0e14 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e994 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X3 X4)) ≠ (M.op (M.op X0 X0) (M.op X1 X2)) ∨ (M.op X5 X5) = X5 ∨ (M.op (M.op X0 (M.op X3 X4)) X5) = (k (M.op X0 (M.op X3 X4)) X5) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e15 (M.op X0 (M.op X3 X4)) X5
           have i₂ := b0e34 X0 X3 X4 X1 X2 (M.op X0 (M.op X3 X4))
           grind)
        | (have i₁ := b0e15 (M.op X4 X4) X1
           have i₂ := b0e34 X4 X1 X2 X4 X4 X5
           grind)
        | exact superpose b0e34 b0e15
        | (have j0 := b0e15 (M.op X0 (M.op X3 X4)) X5
           grind)
        | exact resolve b0e15 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e1016 : ∀ X0 X3 X4 X5 : G, (M.op X5 X5) = X5 ∨ (M.op (M.op X0 (M.op X3 X4)) X5) = (k (M.op X0 (M.op X3 X4)) X5) := by
        intro X0 X3 X4 X5
        first
        | (have j0 := b0e994 X0 x x X3 X4 X5
           grind)
        | (have r₁ := b0e994 X0 x x x x X5
           have r₂ := b0e11 X0 x x (M.op x x)
           grind)
        | exact resolve b0e994 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e994
      have b0e1017 : ∀ X0 X3 X4 X5 : G, (k X5 (M.op X0 (M.op X3 X4))) = X5 := by
        intro X0 X3 X4 X5
        first
        | (have j0 := b0e993 X0 x x X3 X4 X5
           grind)
        | (have r₁ := b0e993 X0 x x x x X5
           have r₂ := b0e11 X0 x x (M.op x x)
           grind)
        | exact resolve b0e993 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e993
      have b0e1100 : ∀ X0 X5 : G, (M.op (M.op X0 (σ y)) X5) = (k (M.op X0 (σ y)) X5) ∨ (M.op X5 X5) = X5 := by
        intro X0 X5
        first
        | (have i₁ := b0e1016 X0 x x X5
           have i₂ := b0e191 X0 x x
           grind)
        | exact superpose b0e191 b0e1016
        | (have j0 := b0e1016 X0 x x X5
           grind)
        | exact resolve b0e1016 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1016
      have b0e1101 : ∀ X0 X5 : G, (k X5 (M.op X0 (σ y))) = X5 := by
        intro X0 X5
        first
        | (have i₁ := b0e1017 X0 x x X5
           have i₂ := b0e191 X0 x x
           grind)
        | exact superpose b0e191 b0e1017
        | exact resolve b0e1017 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1017
      have b0e1173 : ∀ X0 X5 : G, (M.op (M.op X0 y) X5) = (k (M.op X0 y) X5) ∨ (M.op X5 X5) = X5 := by
        intro X0 X5
        first
        | (have i₁ := b0e1100 X0 X5
           have i₂ := b0e323 X0
           grind)
        | exact superpose b0e323 b0e1100
        | (have j0 := b0e1100 X0 X5
           grind)
        | exact resolve b0e1100 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1100
      have b0e1174 : ∀ X0 X5 : G, (k X5 (M.op X0 y)) = X5 := by
        intro X0 X5
        first
        | (have i₁ := b0e1101 X0 X5
           have i₂ := b0e323 X0
           grind)
        | exact superpose b0e323 b0e1101
        | exact resolve b0e1101 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1101
      have b0e1212 : ∀ X0 X5 : G, (M.op X0 y) = (k (M.op X0 y) X5) ∨ (M.op X5 X5) = X5 := by
        intro X0 X5
        first
        | (have i₁ := b0e1173 X0 X5
           have i₂ := b0e353 X0 X5
           grind)
        | exact superpose b0e353 b0e1173
        | (have j0 := b0e1173 X0 X5
           grind)
        | exact resolve b0e1173 b0e353
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1173
      have b0e1232 : ∀ X0 X5 : G, (M.op X0 y) = (k (M.op X0 y) X5) := by
        intro X0 X5
        first
        | (have j0 := b0e1212 X0 X5
           have j1 := b0e14 (M.op X0 y) X5
           grind)
        | (have r₁ := b0e1212 X0 x
           have r₂ := b0e14 X0 x
           grind)
        | exact resolve b0e1212 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1212
      have b0e1262 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e25 X0 (M.op X1 y)
           have i₂ := b0e1174 X1 (τ X0)
           grind)
        | exact superpose b0e1174 b0e25
        | exact resolve b0e25 b0e1174
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1263 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 y))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e1262 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e1262
        | exact resolve b0e1262 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1262
      have b0e1821 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X3) = X2 ∨ (M.op X0 X3) = (k X3 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e121 X3 X2 X0
           grind)
        | exact superpose b0e121 b0e14
        | (have j0 := b0e14 X1 X0
           have j1 := b0e121 X3 X2 X0
           grind)
        | (have r₁ := b0e14 X0 X2
           have r₂ := b0e121 X0 X1 X2
           grind)
        | exact resolve b0e14 b0e121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1836 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 X0) = (M.op X1 (M.op X2 X3)) ∨ (k X4 X5) = X4 ∨ (k X5 X0) = (M.op X0 X5) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e37 X1 X2 X3 X0 X0
           have i₂ := b0e121 X5 X4 X0
           grind)
        | exact superpose b0e121 b0e37
        | (have j1 := b0e121 X5 X4 X0
           grind)
        | exact resolve b0e37 b0e121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e121
      have b0e1874 : ∀ X0 X1 X2 X3 : G, (k X1 X0) = X1 ∨ (k X2 X3) = X2 ∨ (M.op X0 X3) = (k X3 X0) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e1821 X0 X1 X2 X3
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1821
      have b0e1886 : ∀ X0 X1 X4 X5 : G, (M.op X1 X0) = (M.op X1 (σ y)) ∨ (k X4 X5) = X4 ∨ (k X5 X0) = (M.op X0 X5) := by
        intro X0 X1 X4 X5
        first
        | (have i₁ := b0e1836 X0 X1 x x X4 X5
           have i₂ := b0e191 X1 x x
           grind)
        | exact superpose b0e191 b0e1836
        | (have j0 := b0e1836 X0 X1 x x X4 X5
           grind)
        | exact resolve b0e1836 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1836
      have b0e1906 : ∀ X0 X1 X4 X5 : G, (M.op X1 X0) = (M.op X1 y) ∨ (k X4 X5) = X4 ∨ (k X5 X0) = (M.op X0 X5) := by
        intro X0 X1 X4 X5
        first
        | (have i₁ := b0e1886 X0 X1 X4 X5
           have i₂ := b0e323 X1
           grind)
        | exact superpose b0e323 b0e1886
        | (have j0 := b0e1886 X0 X1 X4 X5
           grind)
        | exact resolve b0e1886 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1886
      have b0e2031 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (k X3 X4) = X3 ∨ (k (M.op X0 X1) X4) = (M.op X4 (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 (M.op X1 X2) X1 X2 X3
           have i₂ := b0e123 X0 X1 (M.op X1 X2)
           grind)
        | exact superpose b0e123 b0e11
        | (have j1 := b0e123 X4 X3 (M.op X0 X1)
           grind)
        | exact resolve b0e11 b0e123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2069 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X0 X1) X4) = (M.op X4 (σ y)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (k X3 X4) = X3 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e2031 X0 X1 X2 X3 X4
           have i₂ := b0e191 X4 X0 X1
           grind)
        | exact superpose b0e191 b0e2031
        | (have j0 := b0e2031 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e2031 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2031
      have b0e2097 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X0 X1) X4) = (M.op X4 y) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (k X3 X4) = X3 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e2069 X0 X1 X2 X3 X4
           have i₂ := b0e323 X4
           grind)
        | exact superpose b0e323 b0e2069
        | (have j0 := b0e2069 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e2069 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2069
      have b0e3320 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X3 (M.op X4 X5)) = (M.op X3 X6) ∨ (k X0 X3) = (M.op X3 X0) := by
        intro X0 X1 X2 X3 X4 X5 X6
        first
        | (have i₁ := b0e32 X4 X1 X4
           have i₂ := b0e105 X0 X1 X2 X3 X4
           grind)
        | exact superpose b0e105 b0e32
        | (have j1 := b0e105 X3 X4 X5 X6 X0
           grind)
        | exact resolve b0e32 b0e105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3371 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e105 (M.op X0 X1) X1 X2 x (M.op X0 X1)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e105
      have b0e3377 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e3371 X0 X1 x
           have j1 := b0e116 X0 X1 (M.op X0 X1) (M.op X0 X1)
           grind)
        | (have r₁ := b0e3371 X0 X1 x
           have r₂ := b0e116 X0 X1 x x
           grind)
        | (have r₁ := b0e3371 X0 X1 (M.op X0 X1)
           have r₂ := b0e116 X0 X1 x (M.op X0 X1)
           grind)
        | exact resolve b0e3371 b0e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3371
      have b0e3409 : ∀ X0 X1 X2 X3 X6 : G, (M.op X3 (σ y)) = (M.op X3 X6) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (k X0 X3) = (M.op X3 X0) := by
        intro X0 X1 X2 X3 X6
        first
        | (have i₁ := b0e3320 X0 X1 X2 X3 x x X6
           have i₂ := b0e191 X3 x x
           grind)
        | exact superpose b0e191 b0e3320
        | (have j0 := b0e3320 X0 X1 X2 X3 x x X6
           grind)
        | exact resolve b0e3320 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3320
      have b0e3472 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e3377 X0 X1
           have i₂ := b0e191 (M.op X0 X1) X0 X1
           grind)
        | exact superpose b0e191 b0e3377
        | (have j0 := b0e3377 X0 X1
           grind)
        | exact resolve b0e3377 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3377
      have b0e3503 : ∀ X0 X1 X2 X3 X6 : G, (M.op X3 y) = (M.op X3 X6) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (k X0 X3) = (M.op X3 X0) := by
        intro X0 X1 X2 X3 X6
        first
        | (have i₁ := b0e3409 X0 X1 X2 X3 X6
           have i₂ := b0e323 X3
           grind)
        | exact superpose b0e323 b0e3409
        | (have j0 := b0e3409 X0 X1 X2 X3 X6
           grind)
        | exact resolve b0e3409 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3409
      have b0e3557 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) y) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e3472 X0 X1
           have i₂ := b0e323 (M.op X0 X1)
           grind)
        | exact superpose b0e323 b0e3472
        | (have j0 := b0e3472 X0 X1
           grind)
        | exact resolve b0e3472 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3472
      have b0e3600 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e3557 X0 X1
           have i₂ := b0e191 (M.op X0 X1) X0 X1
           grind)
        | exact superpose b0e191 b0e3557
        | (have j0 := b0e3557 X0 X1
           grind)
        | exact resolve b0e3557 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3557
      have b0e3628 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e3600 X0 X1
           have i₂ := b0e323 (M.op X0 X1)
           grind)
        | exact superpose b0e323 b0e3600
        | (have j0 := b0e3600 X0 X1
           grind)
        | exact resolve b0e3600 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3600
      have b0e4631 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (σ y)) = (k (M.op X0 X1) X2) ∨ (M.op X2 X2) = X2 ∨ (k X3 X4) = X3 ∨ (k (M.op X0 X1) X4) = (M.op X4 (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e63 (M.op X1 X2) X1 X2 X3
           have i₂ := b0e123 X0 X1 (M.op X1 X2)
           grind)
        | exact superpose b0e123 b0e63
        | (have j0 := b0e63 X0 X1 X2 X2
           have j1 := b0e123 X4 X3 X2
           grind)
        | exact resolve b0e63 b0e123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63 b0e123
      have b0e4686 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (σ y)) = (k (M.op X0 X1) X2) ∨ (M.op X2 X2) = X2 ∨ (k X3 X4) = X3 ∨ (k (M.op X0 X1) X4) = (M.op X4 (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have j0 := b0e4631 X0 X1 X2 X3 X4
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4631
      have b0e4741 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) y) = (k (M.op X0 X1) X2) ∨ (M.op X2 X2) = X2 ∨ (k X3 X4) = X3 ∨ (k (M.op X0 X1) X4) = (M.op X4 (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e4686 X0 X1 X2 X3 X4
           have i₂ := b0e323 (M.op X0 X1)
           grind)
        | exact superpose b0e323 b0e4686
        | (have j0 := b0e4686 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e4686 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4686
      have b0e4813 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X0 X1) X4) = (M.op X4 (σ y)) ∨ (M.op (M.op X0 X1) y) = (k (M.op X0 X1) X2) ∨ (M.op X2 X2) = X2 ∨ (k X3 X4) = X3 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e4741 X0 X1 X2 X3 X4
           have i₂ := b0e191 X4 X0 X1
           grind)
        | exact superpose b0e191 b0e4741
        | (have j0 := b0e4741 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e4741 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4741
      have b0e4866 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X0 X1) X4) = (M.op X4 y) ∨ (M.op (M.op X0 X1) y) = (k (M.op X0 X1) X2) ∨ (M.op X2 X2) = X2 ∨ (k X3 X4) = X3 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e4813 X0 X1 X2 X3 X4
           have i₂ := b0e323 X4
           grind)
        | exact superpose b0e323 b0e4813
        | (have j0 := b0e4813 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e4813 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4813
      have b0e5674 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e124 X0 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e124
      have b0e5675 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e5674 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5674
      have b0e5676 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e5675 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5675
      have b0e7099 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op X3 X4) = (M.op (M.op X3 X4) X5) ∨ (k (M.op X0 X1) (M.op X3 X4)) = (M.op (M.op X3 X4) (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e11 (M.op X1 X2) X1 X2 X3
           have i₂ := b0e109 X0 X1 X2 (M.op X1 X2)
           grind)
        | exact superpose b0e109 b0e11
        | (have j1 := b0e109 X3 X4 X5 (M.op X0 X1)
           grind)
        | exact resolve b0e11 b0e109
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109
      have b0e7153 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (M.op X0 X1) (M.op X3 X4)) = (M.op (M.op X3 X4) (σ y)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op X3 X4) = (M.op (M.op X3 X4) X5) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e7099 X0 X1 X2 X3 X4 X5
           have i₂ := b0e191 (M.op X3 X4) X0 X1
           grind)
        | exact superpose b0e191 b0e7099
        | (have j0 := b0e7099 X0 X1 X2 X0 X1 X2
           grind)
        | exact resolve b0e7099 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7099
      have b0e7225 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (M.op X0 X1) (M.op X3 X4)) = (M.op (M.op X3 X4) y) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op X3 X4) = (M.op (M.op X3 X4) X5) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e7153 X0 X1 X2 X3 X4 X5
           have i₂ := b0e323 (M.op X3 X4)
           grind)
        | exact superpose b0e323 b0e7153
        | (have j0 := b0e7153 X0 X1 X2 X0 X1 X2
           grind)
        | exact resolve b0e7153 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7153
      have b0e7593 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X3 X4) = (M.op (M.op X3 X4) X5) ∨ (M.op X0 (M.op X3 X4)) = (k (M.op X3 X4) X0) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e32 X3 X1 X4
           have i₂ := b0e116 X0 X1 X2 X3
           grind)
        | exact superpose b0e116 b0e32
        | (have j1 := b0e116 X3 X4 X5 X0
           grind)
        | exact resolve b0e32 b0e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116
      have b0e7714 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (σ y)) = (k (M.op X3 X4) X0) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X3 X4) = (M.op (M.op X3 X4) X5) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e7593 X0 X1 X2 X3 X4 X5
           have i₂ := b0e191 X0 X3 X4
           grind)
        | exact superpose b0e191 b0e7593
        | (have j0 := b0e7593 X0 X1 X2 X3 X4 X5
           grind)
        | exact resolve b0e7593 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7593
      have b0e7811 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 y) = (k (M.op X3 X4) X0) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X3 X4) = (M.op (M.op X3 X4) X5) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e7714 X0 X1 X2 X3 X4 X5
           have i₂ := b0e323 X0
           grind)
        | exact superpose b0e323 b0e7714
        | (have j0 := b0e7714 X0 X1 X2 X3 X4 X5
           grind)
        | exact resolve b0e7714 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7714
      have b0e8328 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X3 X3) = (M.op X3 (M.op X4 X5)) ∨ (k (M.op X3 X3) X0) = (M.op X0 (M.op X3 X3)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e32 X3 X1 X4
           have i₂ := b0e117 X0 X1 X2 X3
           grind)
        | exact superpose b0e117 b0e32
        | (have j1 := b0e117 X3 X4 X5 X0
           grind)
        | exact resolve b0e32 b0e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117
      have b0e8458 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X3 (σ y)) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (k (M.op X3 X3) X0) = (M.op X0 (M.op X3 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e8328 X0 X1 X2 X3 x x
           have i₂ := b0e191 X3 x x
           grind)
        | exact superpose b0e191 b0e8328
        | (have j0 := b0e8328 X0 X1 X2 X3 x x
           grind)
        | exact resolve b0e8328 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8328
      have b0e8608 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X3 y) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (k (M.op X3 X3) X0) = (M.op X0 (M.op X3 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e8458 X0 X1 X2 X3
           have i₂ := b0e323 X3
           grind)
        | exact superpose b0e323 b0e8458
        | (have j0 := b0e8458 X0 X1 X2 X3
           grind)
        | exact resolve b0e8458 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8458
      have b0e8750 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ y)) = (k (M.op X3 X3) X0) ∨ (M.op X3 X3) = (M.op X3 y) ∨ (M.op X0 X1) = (M.op X0 X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e8608 X0 X1 X2 X3
           have i₂ := b0e191 X0 X3 X3
           grind)
        | exact superpose b0e191 b0e8608
        | (have j0 := b0e8608 X3 X3 y X3
           grind)
        | exact resolve b0e8608 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8608
      have b0e8875 : ∀ X0 X1 X2 X3 : G, (M.op X0 y) = (k (M.op X3 X3) X0) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X3 X3) = (M.op X3 y) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e8750 X0 X1 X2 X3
           have i₂ := b0e323 X0
           grind)
        | exact superpose b0e323 b0e8750
        | (have j0 := b0e8750 X0 X1 X2 X3
           grind)
        | exact resolve b0e8750 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8750
      have b0e9064 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e169 X0 (M.op X1 y)
           have i₂ := b0e1174 X1 (σ X0)
           grind)
        | exact superpose b0e1174 b0e169
        | exact resolve b0e169 b0e1174
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e9089 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 y))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e9064 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e9064
        | exact resolve b0e9064 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9064
      have b0e9310 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e118 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118
      have b0e9311 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e9310 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9310
      have b0e11291 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) ∨ (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e1263 (σ (M.op X0 y)) X0
           have i₂ := b0e5676 (σ (M.op X0 y))
           grind)
        | exact superpose b0e5676 b0e1263
        | (have j1 := b0e5676 (σ (M.op X0 y))
           grind)
        | exact resolve b0e1263 b0e5676
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1263
      have b0e11298 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) (τ (M.op X0 y))) ∨ (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) (τ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e9089 (τ (M.op X0 y)) X0
           have i₂ := b0e5676 (τ (M.op X0 y))
           grind)
        | exact superpose b0e5676 b0e9089
        | (have j1 := b0e5676 (τ (M.op X0 y))
           grind)
        | exact resolve b0e9089 b0e5676
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5676
      have b0e11333 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) (τ (M.op X0 y))) := by
        intro X0
        first
        | (have j0 := b0e11298 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11298
      have b0e11339 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have j0 := b0e11291 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11291
      have b0e14417 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e9311 (τ X0)
           have i₂ := b0e26 X0 (τ X0)
           grind)
        | exact superpose b0e26 b0e9311
        | (have j0 := b0e9311 (τ X0)
           grind)
        | exact resolve b0e9311 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e9311
      have b0e14451 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e14417 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e14417
        | (have j0 := b0e14417 X0
           grind)
        | exact resolve b0e14417 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14417
      have b0e14475 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e14451 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e14451
        | (have j0 := b0e14451 X0
           grind)
        | exact resolve b0e14451 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14451
      have b0e16467 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e1874 X1 X0 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1874
      have b0e16470 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e16467 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16467
      have b0e19345 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X3 X4) = (M.op X3 X5) ∨ (M.op X0 X3) = (k X3 X0) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e32 X3 X1 X4
           have i₂ := b0e230 X0 X1 X2 X3
           grind)
        | exact superpose b0e230 b0e32
        | (have j1 := b0e230 X3 X4 X5 X0
           grind)
        | exact resolve b0e32 b0e230
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e230
      have b0e23050 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (k (M.op X0 X1) X2) ∨ (k X3 X4) = X3 ∨ (M.op X1 X4) = (k X4 X1) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e1232 X1 x
           have i₂ := b0e1906 y X1 X4 x
           grind)
        | (have i₁ := b0e1232 X1 x
           have i₂ := b0e1906 X0 X1 X4 x
           grind)
        | exact superpose b0e1906 b0e1232
        | (have j1 := b0e1906 X1 X1 X3 X4
           grind)
        | exact resolve b0e1232 b0e1906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1232 b0e1906
      have b0e31240 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 X1) = (k X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e169 X0 X1
           have i₂ := b0e16470 (σ X0) X1
           grind)
        | exact superpose b0e16470 b0e169
        | (have j1 := b0e16470 X0 X1
           grind)
        | exact resolve b0e169 b0e16470
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e169
      have b0e31244 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X1 X1) = (k X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e25 X0 X1
           have i₂ := b0e16470 (τ X0) X1
           grind)
        | exact superpose b0e16470 b0e25
        | (have j1 := b0e16470 X0 X1
           grind)
        | exact resolve b0e25 b0e16470
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25 b0e16470
      have b0e31329 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X1 X1) = (k X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e31244 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e31244
        | (have j0 := b0e31244 X0 X1
           grind)
        | exact resolve b0e31244 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31244
      have b0e31331 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 X1) = (k X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e31240 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e31240
        | (have j0 := b0e31240 X0 X1
           grind)
        | exact resolve b0e31240 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31240
      have b0e40915 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e14475 (σ X0)
           have i₂ := b0e31329 (σ X0) X0
           grind)
        | exact superpose b0e31329 b0e14475
        | (have j0 := b0e14475 (σ X0)
           have j1 := b0e31329 X0 X0
           grind)
        | (have r₁ := b0e14475 (σ x)
           have r₂ := b0e31329 (σ x) x
           grind)
        | exact resolve b0e14475 b0e31329
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14475 b0e31329
      have b0e41038 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e40915 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40915
      have b0e41840 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X1 (τ (σ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e31331 X1 (σ X0)
           grind)
        | exact superpose b0e31331 b0e17
        | (have j1 := b0e31331 X1 (σ X0)
           grind)
        | exact resolve b0e17 b0e31331
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31331
      have b0e41873 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e41840 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e41840
        | (have j0 := b0e41840 X0 X1
           grind)
        | exact resolve b0e41840 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41840
      have b0e50236 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 y) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e3503 X0 X1 X2 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3503
      have b0e50245 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e50236 X0 X1 X2
           have j1 := b0e19345 X0 X1 X2 X0 X1 X2
           grind)
        | (have r₁ := b0e50236 X0 X1 X1
           have r₂ := b0e19345 X0 X1 y x x x
           grind)
        | (have r₁ := b0e50236 X0 X1 X2
           have r₂ := b0e19345 X0 y X2 x x x
           grind)
        | (have r₁ := b0e50236 x X1 x
           have r₂ := b0e19345 X0 X1 X2 x x y
           grind)
        | exact resolve b0e50236 b0e19345
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19345 b0e50236
      have b0e60797 : ∀ X0 : G, (M.op (τ (M.op X0 y)) y) = (k (τ (M.op X0 y)) (τ (M.op X0 y))) ∨ (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) y) := by
        intro X0
        first
        | (have i₁ := b0e3628 (τ (M.op X0 y)) (τ (M.op X0 y))
           have i₂ := b0e11333 X0
           grind)
        | exact superpose b0e11333 b0e3628
        | exact resolve b0e3628 b0e11333
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11333
      have b0e61021 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) y) ∨ (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) y) := by
        intro X0
        first
        | (have i₁ := b0e60797 X0
           have i₂ := b0e9089 (τ (M.op X0 y)) X0
           grind)
        | exact superpose b0e9089 b0e60797
        | (have j0 := b0e60797 X0
           grind)
        | exact resolve b0e60797 b0e9089
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9089 b0e60797
      have b0e61022 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) y) := by
        intro X0
        first
        | (have j0 := b0e61021 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61021
      have b0e63420 : ∀ X0 X1 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e353 (τ (M.op X0 y)) X1
           have i₂ := b0e61022 X0
           grind)
        | exact superpose b0e61022 b0e353
        | exact resolve b0e353 b0e61022
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61022
      have b0e89111 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 y) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have j0 := b0e8875 X0 X0 y X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e89115 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b0e89111 X0 x
           have j1 := b0e8875 X0 X0 y X0
           grind)
        | (have r₁ := b0e89111 x x
           have r₂ := b0e8875 x x x x
           grind)
        | (have r₁ := b0e89111 x x
           have r₂ := b0e8875 x x x x
           grind)
        | (have r₁ := b0e89111 x y
           have r₂ := b0e8875 X0 x x x
           grind)
        | exact resolve b0e89111 b0e8875
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8875 b0e89111
      have b0e99839 : ∀ X0 : G, (M.op (σ (M.op X0 y)) y) = (k (σ (M.op X0 y)) (σ (M.op X0 y))) ∨ (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) y) := by
        intro X0
        first
        | (have i₁ := b0e3628 (σ (M.op X0 y)) (σ (M.op X0 y))
           have i₂ := b0e11339 X0
           grind)
        | exact superpose b0e11339 b0e3628
        | exact resolve b0e3628 b0e11339
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3628 b0e11339
      have b0e99868 : ∀ X0 : G, (M.op (σ (M.op X0 y)) y) = (σ (k (M.op X0 y) (M.op X0 y))) ∨ (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) y) := by
        intro X0
        first
        | (have i₁ := b0e99839 X0
           have i₂ := b0e17 (M.op X0 y) (M.op X0 y)
           grind)
        | exact superpose b0e17 b0e99839
        | (have j0 := b0e99839 X0
           grind)
        | exact resolve b0e99839 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e99839
      have b0e100014 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) y) ∨ (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) y) := by
        intro X0
        first
        | (have i₁ := b0e99868 X0
           have i₂ := b0e1174 X0 (M.op X0 y)
           grind)
        | (have i₁ := b0e99868 X0
           have i₂ := b0e1174 X0 (k (M.op X0 y) (M.op X0 y))
           grind)
        | exact superpose b0e1174 b0e99868
        | (have j0 := b0e99868 X0
           grind)
        | exact resolve b0e99868 b0e1174
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1174 b0e99868
      have b0e100015 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) y) := by
        intro X0
        first
        | (have j0 := b0e100014 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100014
      have b0e103472 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e353 (σ (M.op X0 y)) X1
           have i₂ := b0e100015 X0
           grind)
        | exact superpose b0e100015 b0e353
        | exact resolve b0e353 b0e100015
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100015
      have b0e130833 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X3) ∨ (M.op (M.op X0 X1) y) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e7811 (M.op X0 X1) X1 X2 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7811
      have b0e130839 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e130833 X0 X1 X2 x
           have j1 := b0e7225 X0 X1 X2 X0 X1 X2
           grind)
        | (have r₁ := b0e130833 X0 X1 X2 X2
           have r₂ := b0e7225 X0 X1 X2 x x x
           grind)
        | (have r₁ := b0e130833 x x X2 x
           have r₂ := b0e7225 X0 X1 X2 x x x
           grind)
        | exact resolve b0e130833 b0e7225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7225 b0e130833
      have b0e194664 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e324 X1 (σ X0) (σ X0)
           have i₂ := b0e41038 X0
           grind)
        | exact superpose b0e41038 b0e324
        | (have j1 := b0e41038 X0
           grind)
        | exact resolve b0e324 b0e41038
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e324
      have b0e214801 : ∀ X0 : G, (σ X0) = (M.op (σ X0) y) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e41038 X0
           have i₂ := b0e194664 X0 (σ X0)
           grind)
        | exact superpose b0e194664 b0e41038
        | (have j0 := b0e41038 X0
           have j1 := b0e194664 X0 x
           grind)
        | exact resolve b0e41038 b0e194664
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41038 b0e194664
      have b0e214904 : ∀ X0 : G, (σ X0) = (M.op (σ X0) y) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e214801 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e214801
      have b0e216724 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e353 (σ X0) X1
           have i₂ := b0e214904 X0
           grind)
        | exact superpose b0e214904 b0e353
        | (have j1 := b0e214904 X0
           grind)
        | exact resolve b0e353 b0e214904
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e353
      have b0e216766 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e63420 (σ X0) X1
           have i₂ := b0e214904 X0
           grind)
        | exact superpose b0e214904 b0e63420
        | (have j1 := b0e214904 X0
           grind)
        | exact resolve b0e63420 b0e214904
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63420 b0e214904
      have b0e216934 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e216766 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e216766
        | (have j0 := b0e216766 X0 X1
           grind)
        | exact resolve b0e216766 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e216766
      have b0e222173 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (k x x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e216724 x (σ y)
           grind)
        | exact superpose b0e216724 b0e18
        | (have j1 := b0e216724 x x
           grind)
        | exact resolve b0e18 b0e216724
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e216724
      have b0e228528 : ∀ X0 : G, (σ x) ≠ (σ (M.op x X0)) ∨ (M.op x x) = (k x x) ∨ (M.op x x) = (k x x) := by
        intro X0
        first
        | (have i₁ := b0e222173
           have i₂ := b0e50245 x y X0
           grind)
        | (have i₁ := b0e222173
           have i₂ := b0e50245 x X0 y
           grind)
        | exact superpose b0e50245 b0e222173
        | (have j1 := b0e50245 x x x
           grind)
        | exact resolve b0e222173 b0e50245
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50245 b0e222173
      have b0e228529 : ∀ X0 : G, (σ x) ≠ (σ (M.op x X0)) ∨ (M.op x x) = (k x x) := by
        intro X0
        first
        | (have j0 := b0e228528 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228528
      have b0e233435 : (σ x) ≠ (σ x) ∨ (M.op x x) = (k x x) ∨ (M.op x x) = (k x x) := by
        first
        | (have i₁ := b0e228529 x
           have i₂ := b0e216934 x x
           grind)
        | exact superpose b0e216934 b0e228529
        | (have j1 := b0e216934 x x
           grind)
        | exact resolve b0e228529 b0e216934
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e216934 b0e228529
      have b0e233481 : (σ x) ≠ (σ x) ∨ (M.op x x) = (k x x) := by grind
      clear b0e233435
      have b0e233482 : (M.op x x) = (k x x) := by grind
      clear b0e233481
      have b0e270114 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) y) ∨ (M.op X2 y) = (k (M.op X0 X1) X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e4866 X0 X1 X2 (M.op X0 X1) X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4866
      have b0e270246 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) y) ∨ (M.op X2 y) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e270114 X0 X1 X2
           have j1 := b0e14 (M.op X0 X1) X2
           grind)
        | (have r₁ := b0e270114 X0 X1 X1
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e270114 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e270114
      have b0e270265 : ∀ X0 X1 X2 : G, (M.op X2 y) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e270246 X0 X1 X2
           have j1 := b0e2097 X0 X1 X2 (M.op X0 X1) X2
           grind)
        | (have r₁ := b0e270246 X0 X1 X2
           have r₂ := b0e2097 X0 X1 y x x
           grind)
        | exact resolve b0e270246 b0e2097
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2097 b0e270246
      have b0e1125997 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 y) ∨ (M.op X2 y) = (k (M.op X0 X1) X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e270265 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e270265
      have b0e1128112 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (M.op X1 X2) (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1125997 X0 X1 (M.op X0 X0)
           have i₂ := b0e142 X0 y
           grind)
        | exact superpose b0e142 b0e1125997
        | (have j0 := b0e1125997 X1 X2 X0
           grind)
        | (have r₁ := b0e1125997 (M.op X0 X0) X2 X0
           have r₂ := b0e142 X0 X2
           grind)
        | (have r₁ := b0e1125997 X0 y (M.op X0 X0)
           have r₂ := b0e142 X0 y
           grind)
        | exact resolve b0e1125997 b0e142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1135644 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) ∨ (M.op X1 X2) = (k X2 X1) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e23050 X0 X1 X2 (M.op X0 X1) X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23050
      have b0e1135647 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) X2) ∨ (M.op X1 X2) = (k X2 X1) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e1135644 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1135644
      have b0e1138612 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op (M.op X0 X0) y) = (k (M.op X0 X0) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e142 X0 x
           have i₂ := b0e130839 X0 X0 x
           grind)
        | exact superpose b0e130839 b0e142
        | (have j1 := b0e130839 X0 X0 x
           grind)
        | exact resolve b0e142 b0e130839
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142 b0e130839
      have b0e1138614 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e1138612 X0
           have i₂ := b0e31 X0 y
           grind)
        | exact superpose b0e31 b0e1138612
        | (have j0 := b0e1138612 X0
           grind)
        | exact resolve b0e1138612 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e1138612
      have b0e1138616 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e1138614 X0
           have i₂ := b0e323 X0
           grind)
        | exact superpose b0e323 b0e1138614
        | (have j0 := b0e1138614 X0
           grind)
        | exact resolve b0e1138614 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1138614
      have b0e1138618 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 X0) (M.op X0 X0)) := by
        intro X0
        first
        | (have j0 := b0e1138616 X0
           have j1 := b0e1128112 X0 X0 X0
           grind)
        | (have r₁ := b0e1138616 X0
           have r₂ := b0e1128112 X0 X0 X0
           grind)
        | (have r₁ := b0e1138616 y
           have r₂ := b0e1128112 y y y
           grind)
        | exact resolve b0e1138616 b0e1128112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1128112 b0e1138616
      have b0e1138834 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have i₁ := b0e1135647 X0 X0 (M.op X0 X0)
           have i₂ := b0e1138618 X0
           grind)
        | exact superpose b0e1138618 b0e1135647
        | (have j0 := b0e1135647 X0 X0 (M.op X0 X0)
           grind)
        | exact resolve b0e1135647 b0e1138618
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1135647 b0e1138618
      have b0e1139093 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e1138834 X0
           have i₂ := b0e191 X0 X0 X0
           grind)
        | exact superpose b0e191 b0e1138834
        | (have j0 := b0e1138834 X0
           grind)
        | exact resolve b0e1138834 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e191 b0e1138834
      have b0e1139195 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e1139093 X0
           have i₂ := b0e323 X0
           grind)
        | exact superpose b0e323 b0e1139093
        | (have j0 := b0e1139093 X0
           grind)
        | exact resolve b0e1139093 b0e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e323 b0e1139093
      have b0e1139231 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e1139195 X0
           have j1 := b0e1125997 X0 X0 X0
           grind)
        | (have r₁ := b0e1139195 x
           have r₂ := b0e1125997 x x x
           grind)
        | (have r₁ := b0e1139195 y
           have r₂ := b0e1125997 y y y
           grind)
        | exact resolve b0e1139195 b0e1125997
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1125997 b0e1139195
      have b0e1139334 : ∀ X0 X1 : G, (M.op (σ X0) y) = (k (σ (k X0 X0)) (σ X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1139231 (σ X0)
           have i₂ := b0e41873 X0 X1
           grind)
        | exact superpose b0e41873 b0e1139231
        | (have j1 := b0e41873 X0 X1
           grind)
        | exact resolve b0e1139231 b0e41873
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41873
      have b0e1139865 : ∀ X0 X1 : G, (M.op (σ X0) y) = (σ (k (k X0 X0) X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1139334 X0 X1
           have i₂ := b0e17 (k X0 X0) X0
           grind)
        | exact superpose b0e17 b0e1139334
        | (have j0 := b0e1139334 X0 X1
           grind)
        | exact resolve b0e1139334 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1139334
      have b0e1141141 : ∀ X0 : G, (M.op (σ x) y) = (σ (k (M.op x x) x)) ∨ (k X0 x) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1139865 x X0
           have i₂ := b0e233482
           grind)
        | exact superpose b0e233482 b0e1139865
        | (have j0 := b0e1139865 x X0
           grind)
        | exact resolve b0e1139865 b0e233482
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1139865
      have b0e1141160 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) y) ∨ (k X0 x) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1141141 X0
           have i₂ := b0e1139231 x
           grind)
        | exact superpose b0e1139231 b0e1141141
        | (have j0 := b0e1141141 X0
           grind)
        | exact resolve b0e1141141 b0e1139231
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1139231 b0e1141141
      have b0e1141165 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b0e1141160 X0
           grind)
        | (have r₁ := b0e1141160 X0
           have r₂ := b0e438
           grind)
        | exact resolve b0e1141160 b0e438
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1141160
      have b0e1141522 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e89115 x
           have i₂ := b0e1141165 (M.op x x)
           grind)
        | exact superpose b0e1141165 b0e89115
        | (have j0 := b0e89115 x
           grind)
        | exact resolve b0e89115 b0e1141165
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89115
      have b0e1141584 : x = (M.op x x) := by
        first
        | (have i₁ := b0e233482
           have i₂ := b0e1141165 x
           grind)
        | exact superpose b0e1141165 b0e233482
        | exact resolve b0e233482 b0e1141165
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e233482 b0e1141165
      have b0e1141586 : (M.op x y) = (M.op x x) := by grind
      clear b0e1141522
      have b0e1141625 : x = (M.op x y) := by
        first
        | (have i₁ := b0e1141586
           have i₂ := b0e1141584
           grind)
        | exact superpose b0e1141584 b0e1141586
        | exact resolve b0e1141586 b0e1141584
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1141584 b0e1141586
      have b0e1142151 : (σ x) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e438
           have i₂ := b0e1141625
           grind)
        | exact superpose b0e1141625 b0e438
        | exact resolve b0e438 b0e1141625
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e438
      have b0e1142223 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e103472 x x
           have i₂ := b0e1141625
           grind)
        | exact superpose b0e1141625 b0e103472
        | exact resolve b0e103472 b0e1141625
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e103472 b0e1141625
      have b0e1142464 : False := by grind
      exact b0e1142464
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
        have b1e93 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
        have b1e99 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e93 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e93
        have b1e148 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b1e156 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e148 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e148
          | exact resolve b1e148 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e148
        have b1e736 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e156 (σ y)
             have i₂ := b1e99 (σ y)
             grind)
          | exact superpose b1e99 b1e156
          | (have j1 := b1e99 (σ y)
             grind)
          | exact resolve b1e156 b1e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e99 b1e156
        have b1e741 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e736
        have b1e745 : False := by grind
        exact b1e745
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
        have b2e111 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
        have b2e116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e111 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e111
        have b2e143 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b2e148 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e143 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e143
          | exact resolve b2e143 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e143
        have b2e524 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e148 (σ y)
             have i₂ := b2e116 (σ y)
             grind)
          | exact superpose b2e116 b2e148
          | (have j1 := b2e116 (σ y)
             grind)
          | exact resolve b2e148 b2e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e116 b2e148
        have b2e527 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e524
        have b2e531 : False := by grind
        exact b2e531
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
        have b3e39 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (σ y) (σ y) X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e16 (σ y) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 (σ y) X0
             grind)
          | (have r₁ := b3e16 (σ y) x
             have r₂ := b3e22
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b3e49 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e78 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
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
        have b3e100 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e78 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e196 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e39 (σ y) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e39
          | exact resolve b3e39 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e210 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (σ y)) ∨ (k X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X1 (M.op X0 X0)
             have i₂ := b3e39 X0 (M.op X0 X0)
             grind)
          | exact superpose b3e39 b3e15
          | (have j0 := b3e15 X1 (M.op X0 X0)
             grind)
          | (have r₁ := b3e15 X0 (M.op (σ y) (σ y))
             have r₂ := b3e39 (σ y) (M.op (σ y) (σ y))
             grind)
          | exact resolve b3e15 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e638 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op (σ y) (M.op X0 X0)) = (k (σ y) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e39 X0 (M.op X0 X0)
             have i₂ := b3e52 (M.op X0 X0)
             grind)
          | exact superpose b3e52 b3e39
          | (have j1 := b3e52 (M.op X0 X0)
             grind)
          | exact resolve b3e39 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e658 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e638 X0
             have i₂ := b3e196 (M.op X0 X0)
             grind)
          | exact superpose b3e196 b3e638
          | (have j0 := b3e638 X0
             grind)
          | exact resolve b3e638 b3e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e638
        have b3e681 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b3e658 X0
             have j1 := b3e210 X0 (σ y)
             grind)
          | (have r₁ := b3e658 X0
             have r₂ := b3e210 X0 x
             grind)
          | (have r₁ := b3e658 (σ y)
             have r₂ := b3e210 (σ y) x
             grind)
          | exact resolve b3e658 b3e210
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e210 b3e658
        have b3e1798 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e681 X0
             have i₂ := b3e52 X0
             grind)
          | exact superpose b3e52 b3e681
          | (have j1 := b3e52 X0
             grind)
          | exact resolve b3e681 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e681
        have b3e1818 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ y) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e1798 X0
             have i₂ := b3e196 X0
             grind)
          | exact superpose b3e196 b3e1798
          | (have j0 := b3e1798 X0
             grind)
          | exact resolve b3e1798 b3e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e196 b3e1798
        have b3e1819 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
          intro X0
          first
          | (have j0 := b3e1818 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1818
        have b3e2103 : ∀ X0 : G, (σ y) = (σ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 y X0
             have i₂ := b3e1819 (σ X0)
             grind)
          | exact superpose b3e1819 b3e18
          | exact resolve b3e18 b3e1819
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1819
        have b3e2423 : ∀ X0 : G, (k y X0) = (τ (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e13 (k y X0)
             have i₂ := b3e2103 X0
             grind)
          | exact superpose b3e2103 b3e13
          | exact resolve b3e13 b3e2103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2103
        have b3e2424 : ∀ X0 : G, y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e2423 X0
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e2423
          | exact resolve b3e2423 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2423
        have b3e4528 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e100 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e100
        have b3e4529 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e4528 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4528
        have b3e4530 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e4529 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4529
        have b3e10437 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e2424 y
             have i₂ := b3e4530 y
             grind)
          | exact superpose b3e4530 b3e2424
          | (have j1 := b3e4530 y
             grind)
          | exact resolve b3e2424 b3e4530
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2424 b3e4530
        have b3e10439 : y = (M.op y y) := by grind
        clear b3e10437
        have b3e10507 : False := by grind
        exact b3e10507
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
            intro X0 X1 X2 X3
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e35 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ x) (σ x) X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = (M.op x X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 x X0 X1 X2
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e50 : ∀ X0 X3 : G, (M.op x X0) = (M.op x X3) := by
            intro X0 X3
            first
            | (have i₁ := b4e40 x x X3
               have i₂ := b4e40 x x X0
               grind)
            | (have i₁ := b4e40 X0 x x
               have i₂ := b4e40 X0 x (M.op X0 x)
               grind)
            | exact superpose b4e40 b4e40
            | exact resolve b4e40 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e89 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e22
               have i₂ := b4e50 x X0
               grind)
            | (have i₁ := b4e22
               have i₂ := b4e50 X0 x
               grind)
            | exact superpose b4e50 b4e22
            | exact resolve b4e22 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e190 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e35 (σ x) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e35
            | exact resolve b4e35 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e220 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e190 (σ y)
               grind)
            | exact superpose b4e190 b4e20
            | exact resolve b4e20 b4e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e190
          have b4e231 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e220
               have i₂ := b4e89 y
               grind)
            | exact superpose b4e89 b4e220
            | exact resolve b4e220 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89 b4e220
          have b4e232 : False := by grind
          exact b4e232
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
          have b5e82 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e76 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e479 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e34 (σ x)
               have i₂ := b5e82 (σ x)
               grind)
            | exact superpose b5e82 b5e34
            | (have j1 := b5e82 (σ x)
               grind)
            | exact resolve b5e34 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e82
          have b5e482 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e479
          have b5e486 : False := by grind
          exact b5e486
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
        have b6e86 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
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
        have b6e94 : ∀ X0 : G, (M.op y X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e86 X0
             grind)
          | (have r₁ := b6e86 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e86 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e86 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e6720 : y ≠ y ∨ y = (M.op y y) := by
          first
          | (have j0 := b6e94 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e94
        have b6e6721 : y = (M.op y y) := by grind
        clear b6e6720
        have b6e6729 : False := by grind
        exact b6e6729
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b7e37 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ x) (σ x) X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op X3 X4)) = (M.op (M.op X0 (M.op X1 X2)) X5) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e13 (M.op X0 X0) X3 X4 X5
               have i₂ := b7e13 X0 X1 X2 (M.op X0 X0)
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e44 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e13 X0 X1 X2 x
               have i₂ := b7e13 X0 X3 X4 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e81 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e23
               have i₂ := b7e18 (σ y) X0
               grind)
            | exact superpose b7e18 b7e23
            | (have j1 := b7e18 X0 X0
               grind)
            | (have r₁ := b7e23
               have r₂ := b7e18 X0 (σ y)
               grind)
            | (have r₁ := b7e23
               have r₂ := b7e18 (σ y) x
               grind)
            | exact resolve b7e23 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e87 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b7e81 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e130 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 X1 X2 x
               have i₂ := b7e37 X0 x
               grind)
            | exact superpose b7e37 b7e13
            | exact resolve b7e13 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e517 : (σ y) = (M.op x (σ y)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e34 (σ y)
               have i₂ := b7e87 x
               grind)
            | exact superpose b7e87 b7e34
            | (have j1 := b7e87 x
               grind)
            | exact resolve b7e34 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e518 : (σ (σ y)) = (σ (M.op x (σ y))) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e30 (σ y)
               have i₂ := b7e87 x
               grind)
            | exact superpose b7e87 b7e30
            | (have j1 := b7e87 x
               grind)
            | exact resolve b7e30 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e521 : (σ (σ y)) = (σ (M.op x (σ y))) := by
            first
            | (have r₁ := b7e518
               have r₂ := b7e22
               grind)
            | exact resolve b7e518 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e518
          have b7e522 : (σ y) = (M.op x (σ y)) := by
            first
            | (have r₁ := b7e517
               have r₂ := b7e22
               grind)
            | exact resolve b7e517 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e517
          have b7e741 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X3 X4)) ≠ (M.op (M.op X0 X0) (M.op X1 X2)) ∨ (k X5 (M.op X0 (M.op X3 X4))) = X5 := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e16 X5 (M.op X0 (M.op X3 X4))
               have i₂ := b7e43 X0 X3 X4 X1 X2 (M.op X0 (M.op X3 X4))
               grind)
            | (have i₁ := b7e16 X0 (M.op X4 X4)
               have i₂ := b7e43 X4 X1 X2 X4 X4 X5
               grind)
            | exact superpose b7e43 b7e16
            | (have j0 := b7e16 X5 (M.op X0 (M.op X3 X4))
               grind)
            | exact resolve b7e16 b7e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e762 : ∀ X0 X3 X4 X5 : G, (k X5 (M.op X0 (M.op X3 X4))) = X5 := by
            intro X0 X3 X4 X5
            first
            | (have j0 := b7e741 X0 x x X3 X4 X5
               grind)
            | (have r₁ := b7e741 X0 x x x x X5
               have r₂ := b7e13 X0 x x (M.op x x)
               grind)
            | exact resolve b7e741 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e741
          have b7e833 : ∀ X0 X5 : G, (k X5 (M.op X0 (σ x))) = X5 := by
            intro X0 X5
            first
            | (have i₁ := b7e762 X0 x x X5
               have i₂ := b7e130 X0 x x
               grind)
            | exact superpose b7e130 b7e762
            | exact resolve b7e762 b7e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e762
          have b7e1216 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e44 X0 X1 X2 x (σ y)
               have i₂ := b7e522
               grind)
            | exact superpose b7e522 b7e44
            | exact resolve b7e44 b7e522
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44 b7e522
          have b7e1217 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e1216 X0 x x
               have i₂ := b7e130 X0 x x
               grind)
            | exact superpose b7e130 b7e1216
            | exact resolve b7e1216 b7e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e130 b7e1216
          have b7e2192 : ∀ X0 : G, (σ (k X0 (M.op x (σ y)))) = (k (σ X0) (σ (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 (M.op x (σ y))
               have i₂ := b7e521
               grind)
            | exact superpose b7e521 b7e19
            | exact resolve b7e19 b7e521
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e521
          have b7e2197 : ∀ X0 : G, (σ (k X0 (M.op x (σ y)))) = (σ (k X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e2192 X0
               have i₂ := b7e19 X0 (σ y)
               grind)
            | exact superpose b7e19 b7e2192
            | exact resolve b7e2192 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2192
          have b7e2200 : ∀ X0 : G, (σ (k X0 (σ y))) = (σ (k X0 (M.op x (σ x)))) := by
            intro X0
            first
            | (have i₁ := b7e2197 X0
               have i₂ := b7e1217 x
               grind)
            | exact superpose b7e1217 b7e2197
            | exact resolve b7e2197 b7e1217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1217 b7e2197
          have b7e2203 : ∀ X0 : G, (σ X0) = (σ (k X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e2200 X0
               have i₂ := b7e833 x X0
               grind)
            | (have i₁ := b7e2200 X0
               have i₂ := b7e833 X0 (k X0 (M.op x (σ x)))
               grind)
            | exact superpose b7e833 b7e2200
            | exact resolve b7e2200 b7e833
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e833 b7e2200
          have b7e2634 : ∀ X0 : G, (τ (σ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e14 (k X0 (σ y))
               have i₂ := b7e2203 X0
               grind)
            | exact superpose b7e2203 b7e14
            | exact resolve b7e14 b7e2203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2203
          have b7e2635 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e2634 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e2634
            | exact resolve b7e2634 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2634
          have b7e3105 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e87 (σ y)
               have i₂ := b7e2635 (σ y)
               grind)
            | exact superpose b7e2635 b7e87
            | (have j0 := b7e87 (σ y)
               grind)
            | exact resolve b7e87 b7e2635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87 b7e2635
          have b7e3113 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b7e3105
          have b7e3120 : False := by grind
          exact b7e3120
        · have b8e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X0) X3) := by
            intro X0 X1 X2 X3
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
          have b8e29 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X4) := by
            intro X0 X1 X4
            first
            | (have i₁ := b8e13 X0 x x X4
               have i₂ := b8e13 X0 x x X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e65 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
          have b8e71 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e65 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e234 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e29 X0 X1 x
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e29
            | (have j1 := b8e71 X0
               grind)
            | exact resolve b8e29 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29
          have b8e17801 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e234 (σ x) (σ x) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e234 (σ x) X0 (σ x)
               grind)
            | exact superpose b8e234 b8e24
            | (have j1 := b8e234 (σ x) x x
               grind)
            | exact resolve b8e24 b8e234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e17833 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b8e71 X0
               have i₂ := b8e234 X0 X0 X1
               grind)
            | (have i₁ := b8e71 X0
               have i₂ := b8e234 X0 X1 X0
               grind)
            | exact superpose b8e234 b8e71
            | (have j0 := b8e71 X0
               have j1 := b8e234 X0 X1 x
               grind)
            | exact resolve b8e71 b8e234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71 b8e234
          have b8e18081 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b8e17833 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17833
          have b8e18106 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j1 := b8e18081 (σ x) x
               grind)
            | (have r₁ := b8e17801 x
               have r₂ := b8e18081 (σ x) x
               grind)
            | exact resolve b8e17801 b8e18081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17801 b8e18081
          have b8e18114 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e18106
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e18106
            | exact resolve b8e18106 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18106
          have b8e26061 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e18114
               grind)
            | exact superpose b8e18114 b8e20
            | exact resolve b8e20 b8e18114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18114
          have b8e26972 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e26061
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e26061
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e26061 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26061
          have b8e26989 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e26972
          have b8e26996 : y = (M.op y y) := by
            first
            | (have r₁ := b8e26989
               have r₂ := b8e22
               grind)
            | exact resolve b8e26989 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26989
          have b8e26997 : False := by grind
          exact b8e26997

/-- `Equation4518`: `x ◇ (y ◇ z) = (x ◇ w) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pxx_pxx_pxy_Equation4518 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4518 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4518.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
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
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op x x) := by grind
        have b0e21 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b0e22 : x = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : x = y := by
          first
          | (have i₁ := b0e20
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e20
          | exact resolve b0e20 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e31 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e24
             grind)
          | exact superpose b0e24 b0e19
          | exact resolve b0e19 b0e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e32 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e31
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e31
          | exact resolve b0e31 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e31
        have b0e33 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b0e32
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e32
          | exact resolve b0e32 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e32
        have b0e34 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b0e33
             have i₂ := b0e24
             grind)
          | exact superpose b0e24 b0e33
          | exact resolve b0e33 b0e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24 b0e33
        have b0e35 : False := by grind
        exact b0e35
      · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
        · have b1e23 : x ≠ (M.op x x) := by grind
          have b1e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e26 : False := by grind
          exact b1e26
        · have b2e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op x x) := by grind
          have b2e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b2e24 : x ≠ (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e26 : x ≠ y := by
            first
            | (have i₁ := b2e24
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e24
            | exact resolve b2e24 b2e21
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
          have b2e39 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X0 (σ x) (σ x) X1
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e13
            | exact resolve b2e13 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e41 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X0 X2 X3 (M.op x x)
               have i₂ := b2e13 X0 x x X1
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e42 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op X4 X5)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X3)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b2e13 (M.op X0 X3) X4 X5 X0
               have i₂ := b2e13 X0 X1 X2 X3
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e43 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ y) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 (σ x) X0 X1 (σ x)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e13
            | exact resolve b2e13 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e44 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y x) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 x X0 X1 x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e45 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e13 X0 X1 X2 x
               have i₂ := b2e13 X0 X3 X4 x
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e49 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b2e44 x x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e44
            | exact resolve b2e44 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e44
          have b2e84 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X1 X2 X3 X1
               have i₂ := b2e18 X1 X0
               grind)
            | (have i₁ := b2e13 X0 X1 X2 X3
               have i₂ := b2e18 X0 (M.op X0 X3)
               grind)
            | exact superpose b2e18 b2e13
            | (have j1 := b2e18 X1 X0
               grind)
            | exact resolve b2e13 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e99 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k X0 (τ X1))
               have i₂ := b2e31 X1 X0
               grind)
            | exact superpose b2e31 b2e14
            | exact resolve b2e14 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e31
          have b2e104 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 (σ y)) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e39 (M.op X0 X1) X0
               have i₂ := b2e39 X0 X1
               grind)
            | exact superpose b2e39 b2e39
            | exact resolve b2e39 b2e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e110 : (M.op (M.op x y) y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b2e39 y x
               have i₂ := b2e49
               grind)
            | exact superpose b2e49 b2e39
            | exact resolve b2e39 b2e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e112 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X0 X1 X2 x
               have i₂ := b2e39 X0 x
               grind)
            | exact superpose b2e39 b2e13
            | exact resolve b2e13 b2e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e121 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e104 X0 X1
               have i₂ := b2e112 (M.op X0 (σ y)) X0 X1
               grind)
            | exact superpose b2e112 b2e104
            | exact resolve b2e104 b2e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e104
          have b2e257 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e45 X0 X1 X2 x x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e45
            | exact resolve b2e45 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e297 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e39 (M.op X0 X1) X2
               have i₂ := b2e45 (M.op (M.op X0 X1) X2) X0 X1 X3 X4
               grind)
            | (have i₁ := b2e39 (M.op X0 X1) X2
               have i₂ := b2e45 (M.op (M.op X0 X1) X2) X3 X4 X0 X1
               grind)
            | exact superpose b2e45 b2e39
            | exact resolve b2e39 b2e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e45
          have b2e301 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op (M.op X0 X1) X2) (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e297 X0 X1 X2 x x
               have i₂ := b2e112 (M.op (M.op X0 X1) X2) x x
               grind)
            | exact superpose b2e112 b2e297
            | exact resolve b2e297 b2e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e297
          have b2e351 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e257 X0 (σ x) (σ x)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e257
            | exact resolve b2e257 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e366 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 y) := by
            intro X0 X3
            first
            | (have i₁ := b2e13 X0 x x X3
               have i₂ := b2e257 X0 x x
               grind)
            | exact superpose b2e257 b2e13
            | exact resolve b2e13 b2e257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e416 : (M.op (σ y) (σ x)) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e257 (σ x) x x
               have i₂ := b2e43 x x
               grind)
            | exact superpose b2e43 b2e257
            | exact resolve b2e257 b2e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e43 b2e257
          have b2e460 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e351 (σ x)
               grind)
            | exact superpose b2e351 b2e20
            | exact resolve b2e20 b2e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e509 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X0 (σ y)) (M.op X0 X1)) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e41 (M.op X0 X1) X0 X2 X3
               have i₂ := b2e39 X0 X1
               grind)
            | exact superpose b2e39 b2e41
            | exact resolve b2e41 b2e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e39 b2e41
          have b2e596 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X0 (σ y)) (M.op X0 X1)) (σ y)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e509 X0 X1 X2 X3
               have i₂ := b2e112 (M.op (M.op X0 (σ y)) (M.op X0 X1)) X0 X1
               grind)
            | exact superpose b2e112 b2e509
            | exact resolve b2e509 b2e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e509
          have b2e631 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e596 X0 X1 X2 X3
               have i₂ := b2e121 (M.op X0 (σ y)) (M.op X0 X1)
               grind)
            | exact superpose b2e121 b2e596
            | exact resolve b2e596 b2e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e596
          have b2e655 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e631 X0 X1 X2 X3
               have i₂ := b2e301 X0 (σ y) (σ y)
               grind)
            | exact superpose b2e301 b2e631
            | exact resolve b2e631 b2e301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e301 b2e631
          have b2e673 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 (σ y)) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e655 X0 X1 X2 X3
               have i₂ := b2e351 (M.op X0 (σ y))
               grind)
            | exact superpose b2e351 b2e655
            | exact resolve b2e655 b2e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e655
          have b2e682 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 y) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e673 X0 X1 X2 X3
               have i₂ := b2e351 X0
               grind)
            | exact superpose b2e351 b2e673
            | exact resolve b2e673 b2e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e673
          have b2e687 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 y) y) := by
            intro X0 X1
            first
            | (have i₁ := b2e682 X0 X1 x x
               have i₂ := b2e112 (M.op X0 X1) x x
               grind)
            | exact superpose b2e112 b2e682
            | exact resolve b2e682 b2e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e682
          have b2e691 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 y) y) := by
            intro X0 X1
            first
            | (have i₁ := b2e687 X0 X1
               have i₂ := b2e351 (M.op X0 X1)
               grind)
            | exact superpose b2e351 b2e687
            | exact resolve b2e687 b2e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e687
          have b2e892 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X3)) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e18 (M.op X0 X3) X4
               have i₂ := b2e42 X0 X1 X2 X3 X0 X3
               grind)
            | (have i₁ := b2e18 (M.op X0 (M.op X1 X2)) X1
               have i₂ := b2e42 X0 X1 X2 (M.op X1 X2) X4 x
               grind)
            | exact superpose b2e42 b2e18
            | (have j0 := b2e18 (M.op X0 X3) X4
               grind)
            | exact resolve b2e18 b2e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e42
          have b2e951 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (σ y)) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e892 X0 X1 X2 X3 X4
               have i₂ := b2e112 (M.op X0 (M.op X1 X2)) X0 X3
               grind)
            | exact superpose b2e112 b2e892
            | (have j0 := b2e892 X0 X1 X2 X3 X4
               grind)
            | exact resolve b2e892 b2e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e892
          have b2e1023 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (σ y)) (σ y)) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
            intro X0 X3 X4
            first
            | (have i₁ := b2e951 X0 x x X3 X4
               have i₂ := b2e121 X0 (M.op x x)
               grind)
            | exact superpose b2e121 b2e951
            | (have j0 := b2e951 X0 x x X3 X4
               grind)
            | exact resolve b2e951 b2e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e121 b2e951
          have b2e1094 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (σ y)) y) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
            intro X0 X3 X4
            first
            | (have i₁ := b2e1023 X0 X3 X4
               have i₂ := b2e351 (M.op X0 (σ y))
               grind)
            | exact superpose b2e351 b2e1023
            | (have j0 := b2e1023 X0 X3 X4
               grind)
            | exact resolve b2e1023 b2e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1023
          have b2e1163 : ∀ X0 X3 X4 : G, (M.op (M.op X0 y) y) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
            intro X0 X3 X4
            first
            | (have i₁ := b2e1094 X0 X3 X4
               have i₂ := b2e691 X0 (σ y)
               grind)
            | exact superpose b2e691 b2e1094
            | (have j0 := b2e1094 X0 X3 X4
               grind)
            | exact resolve b2e1094 b2e691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e691 b2e1094
          have b2e1226 : ∀ X0 X3 X4 : G, (M.op X4 (σ y)) = X4 ∨ (M.op (M.op X0 y) y) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) := by
            intro X0 X3 X4
            first
            | (have i₁ := b2e1163 X0 X3 X4
               have i₂ := b2e112 X4 X0 X3
               grind)
            | exact superpose b2e112 b2e1163
            | (have j0 := b2e1163 X0 X3 X4
               grind)
            | exact resolve b2e1163 b2e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1163
          have b2e1276 : ∀ X0 X3 X4 : G, (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op (M.op X0 y) y) = X4 ∨ (M.op X4 y) = X4 := by
            intro X0 X3 X4
            first
            | (have i₁ := b2e1226 X0 X3 X4
               have i₂ := b2e351 X4
               grind)
            | exact superpose b2e351 b2e1226
            | (have j0 := b2e1226 X0 X3 X4
               grind)
            | exact resolve b2e1226 b2e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1226
          have b2e1841 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b2e84 X0 X1 X2 X3
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e84
          have b2e1843 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b2e1841 X0 X1 x x
               have i₂ := b2e112 X1 x x
               grind)
            | exact superpose b2e112 b2e1841
            | (have j0 := b2e1841 X0 X1 x x
               grind)
            | (have r₁ := b2e1841 (M.op X0 (σ y)) X0 X1 x
               have r₂ := b2e112 X0 X1 x
               grind)
            | exact resolve b2e1841 b2e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1841
          have b2e1918 : ∀ X0 X1 : G, (M.op X1 y) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b2e1843 X0 X1
               have i₂ := b2e351 X1
               grind)
            | exact superpose b2e351 b2e1843
            | (have j0 := b2e1843 X0 X1
               grind)
            | (have r₁ := b2e1843 (M.op X0 y) X0
               have r₂ := b2e351 X0
               grind)
            | exact resolve b2e1843 b2e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1843
          have b2e2218 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e18 (M.op X0 X1) X2
               have i₂ := b2e112 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b2e112 b2e18
            | (have j0 := b2e18 (M.op X0 X1) X2
               grind)
            | exact resolve b2e18 b2e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e2261 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e2218 X0 X1 X2
               have i₂ := b2e351 (M.op X0 X1)
               grind)
            | exact superpose b2e351 b2e2218
            | (have j0 := b2e2218 X0 X1 X2
               grind)
            | exact resolve b2e2218 b2e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2218
          have b2e2279 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b2e2261 X0 X1 X2
               have j1 := b2e1918 X2 (M.op X0 X1)
               grind)
            | (have r₁ := b2e2261 X0 X1 X0
               have r₂ := b2e1918 X0 (M.op X0 X1)
               grind)
            | (have r₁ := b2e2261 X0 X1 (M.op X1 y)
               have r₂ := b2e1918 (M.op (M.op X0 X1) y) X1
               grind)
            | (have r₁ := b2e2261 X0 X1 y
               have r₂ := b2e1918 (k (M.op X0 X1) y) (M.op X0 X1)
               grind)
            | exact resolve b2e2261 b2e1918
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2261
          have b2e2289 : ∀ X0 X1 X2 : G, (M.op X2 (σ y)) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e2279 X0 X1 X2
               have i₂ := b2e112 X2 X0 X1
               grind)
            | exact superpose b2e112 b2e2279
            | (have j0 := b2e2279 X0 X1 X2
               grind)
            | exact resolve b2e2279 b2e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e112 b2e2279
          have b2e2297 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 y) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e2289 X0 X1 X2
               have i₂ := b2e351 X2
               grind)
            | exact superpose b2e351 b2e2289
            | (have j0 := b2e2289 X0 X1 X2
               grind)
            | exact resolve b2e2289 b2e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2289
          have b2e13612 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op (M.op x y) y) = X0 ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b2e1276 x x x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e1276
            | (have j0 := b2e1276 x x X0
               grind)
            | exact resolve b2e1276 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1276
          have b2e13673 : ∀ X0 : G, (M.op y (σ y)) = X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b2e13612 X0
               have i₂ := b2e110
               grind)
            | exact superpose b2e110 b2e13612
            | (have j0 := b2e13612 X0
               grind)
            | exact resolve b2e13612 b2e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e110 b2e13612
          have b2e13680 : ∀ X0 : G, (M.op y y) = X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b2e13673 X0
               have i₂ := b2e351 y
               grind)
            | exact superpose b2e351 b2e13673
            | (have j0 := b2e13673 X0
               grind)
            | exact resolve b2e13673 b2e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e351 b2e13673
          have b2e13682 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b2e13680 X0
               have j1 := b2e1918 X0 y
               grind)
            | (have r₁ := b2e13680 X0
               have r₂ := b2e1918 X0 y
               grind)
            | (have r₁ := b2e13680 (M.op x y)
               have r₂ := b2e1918 (M.op y y) x
               grind)
            | (have r₁ := b2e13680 y
               have r₂ := b2e1918 (k y y) y
               grind)
            | exact resolve b2e13680 b2e1918
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1918 b2e13680
          have b2e18662 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b2e2297 (σ x) (σ x) x
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e2297
            | (have j0 := b2e2297 X0 x X0
               grind)
            | exact resolve b2e2297 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2297
          have b2e19760 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b2e99 y X0
               have i₂ := b2e18662 X0
               grind)
            | exact superpose b2e18662 b2e99
            | (have j1 := b2e18662 X0
               grind)
            | exact resolve b2e99 b2e18662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e99 b2e18662
          have b2e20137 : (τ (M.op (σ x) y)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e19760 (σ x)
               have i₂ := b2e416
               grind)
            | exact superpose b2e416 b2e19760
            | (have j0 := b2e19760 (σ x)
               grind)
            | exact resolve b2e19760 b2e416
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e416 b2e19760
          have b2e20186 : (k y x) = (τ (M.op (σ x) y)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e20137
               have i₂ := b2e14 x
               grind)
            | exact superpose b2e14 b2e20137
            | exact resolve b2e20137 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e20137
          have b2e26714 : (M.op (σ x) y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e15 (M.op (σ x) y)
               have i₂ := b2e20186
               grind)
            | exact superpose b2e20186 b2e15
            | exact resolve b2e15 b2e20186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e20186
          have b2e30812 : (M.op (σ x) y) = (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b2e26714
               have i₂ := b2e13682 x
               grind)
            | exact superpose b2e13682 b2e26714
            | (have j1 := b2e13682 (σ x)
               grind)
            | exact resolve b2e26714 b2e13682
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e13682 b2e26714
          have b2e30900 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b2e30812
               have i₂ := b2e49
               grind)
            | exact superpose b2e49 b2e30812
            | exact resolve b2e30812 b2e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e49 b2e30812
          have b2e30933 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b2e30900
               have r₂ := b2e460
               grind)
            | exact resolve b2e30900 b2e460
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e460 b2e30900
          have b2e31524 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b2e366 (σ x) y
               have i₂ := b2e30933
               grind)
            | exact superpose b2e30933 b2e366
            | exact resolve b2e366 b2e30933
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e30933
          have b2e31558 : x = (M.op x y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e31524
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e31524
            | exact resolve b2e31524 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e31524
          have b2e32510 : x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e366 x y
               have i₂ := b2e31558
               grind)
            | exact superpose b2e31558 b2e366
            | exact resolve b2e366 b2e31558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e366 b2e31558
          have b2e32544 : (σ x) = (σ y) := by
            first
            | (have r₁ := b2e32510
               have r₂ := b2e24
               grind)
            | exact resolve b2e32510 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e32510
          have b2e33906 : y = (τ (σ x)) := by
            first
            | (have i₁ := b2e14 y
               have i₂ := b2e32544
               grind)
            | exact superpose b2e32544 b2e14
            | exact resolve b2e14 b2e32544
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e32544
          have b2e33986 : x = y := by
            first
            | (have i₁ := b2e33906
               have i₂ := b2e14 x
               grind)
            | exact superpose b2e14 b2e33906
            | exact resolve b2e33906 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e33906
          have b2e34007 : False := by grind
          exact b2e34007
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e21 : y = (M.op x x) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b3e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          have b3e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : x = y := by
            first
            | (have i₁ := b3e21
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e21
            | exact resolve b3e21 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e27 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e23
               have i₂ := b3e26
               grind)
            | exact superpose b3e26 b3e23
            | exact resolve b3e23 b3e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e28 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e27
               grind)
            | exact superpose b3e27 b3e22
            | exact resolve b3e22 b3e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e27
          have b3e29 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e28
               have i₂ := b3e26
               grind)
            | exact superpose b3e26 b3e28
            | exact resolve b3e28 b3e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26 b3e28
          have b3e30 : False := by grind
          exact b3e30
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b4e25 : x ≠ (M.op x x) := by grind
            have b4e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : False := by grind
            exact b4e28
          · have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op x x) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b5e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e29 : y = (k x y) := by grind
            have b5e60 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
            have b5e63 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
            clear b5e60
            have b5e65 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e63
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e63 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e63
            have b5e67 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b5e65
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e65
              | exact resolve b5e65 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e65
            have b5e68 : (σ y) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b5e67
                 have i₂ := b5e29
                 grind)
              | exact superpose b5e29 b5e67
              | exact resolve b5e67 b5e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e29 b5e67
            have b5e69 : False := by grind
            exact b5e69
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op x x) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b6e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : x = y := by
            first
            | (have i₁ := b6e21
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e21
            | exact resolve b6e21 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e27 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e26
               grind)
            | exact superpose b6e26 b6e23
            | exact resolve b6e23 b6e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e28 : x = (k x x) := by grind
          have b6e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X0 X1
               have i₂ := b6e18 (σ X0) (σ X1)
               grind)
            | exact superpose b6e18 b6e19
            | (have j1 := b6e18 (σ X0) (σ X1)
               grind)
            | exact resolve b6e19 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e1809 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e76 x x
               grind)
            | exact superpose b6e76 b6e22
            | (have j1 := b6e76 x x
               grind)
            | (have r₁ := b6e22
               have r₂ := b6e76 x y
               grind)
            | exact resolve b6e22 b6e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e76
          have b6e1902 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b6e1809
          have b6e1951 : (σ y) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b6e1902
               have r₂ := b6e27
               grind)
            | exact resolve b6e1902 b6e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e27 b6e1902
          have b6e1981 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b6e1951
               have i₂ := b6e28
               grind)
            | exact superpose b6e28 b6e1951
            | exact resolve b6e1951 b6e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e28 b6e1951
          have b6e1993 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b6e1981
               have i₂ := b6e26
               grind)
            | exact superpose b6e26 b6e1981
            | exact resolve b6e1981 b6e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26 b6e1981
          have b6e1994 : False := by grind
          exact b6e1994
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b7e25 : x ≠ (M.op x x) := by grind
            have b7e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : False := by grind
            exact b7e28
          · have b8e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op x x) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e29 : y = (k x y) := by grind
            have b8e38 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b8e14 X0 X1 X2 x
                 have i₂ := b8e14 X0 X3 X4 x
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e23
                 have i₂ := b8e19 (σ x) X0
                 grind)
              | (have i₁ := b8e23
                 have i₂ := b8e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b8e19 b8e23
              | (have j1 := b8e19 (σ x) X0
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e19 (σ x) (σ y)
                 grind)
              | exact resolve b8e23 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e181 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e38 X0 X1 X2 x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e38
              | exact resolve b8e38 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e38
            have b8e243 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 y) := by
              intro X0 X3
              first
              | (have i₁ := b8e14 X0 x x X3
                 have i₂ := b8e181 X0 x x
                 grind)
              | exact superpose b8e181 b8e14
              | exact resolve b8e14 b8e181
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e857 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b8e69 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e69
            have b8e858 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b8e857
                 have r₂ := b8e24
                 grind)
              | exact resolve b8e857 b8e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e857
            have b8e859 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e858
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e858
              | exact resolve b8e858 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e858
            have b8e860 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b8e859
                 have i₂ := b8e29
                 grind)
              | exact superpose b8e29 b8e859
              | exact resolve b8e859 b8e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e29 b8e859
            have b8e874 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e181 X0 (σ x) (σ y)
                 have i₂ := b8e860
                 grind)
              | exact superpose b8e860 b8e181
              | exact resolve b8e181 b8e860
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e181
            have b8e1410 : (σ y) = (M.op (σ x) y) := by
              first
              | (have i₁ := b8e860
                 have i₂ := b8e874 (σ x)
                 grind)
              | exact superpose b8e874 b8e860
              | exact resolve b8e860 b8e874
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e860 b8e874
            have b8e1601 : (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b8e243 (σ x) y
                 have i₂ := b8e1410
                 grind)
              | exact superpose b8e1410 b8e243
              | exact resolve b8e243 b8e1410
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e243 b8e1410
            have b8e1602 : False := by grind
            exact b8e1602
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : y ≠ (M.op x x) := by grind
          have b9e22 : y = (M.op y x) := by grind
          have b9e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b9e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e26 : x ≠ y := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e21
            | exact resolve b9e21 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e28 : (σ y) = (k (σ x) (σ y)) := by grind
          have b9e29 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b9e28
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e28
            | exact resolve b9e28 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e28
          have b9e34 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b9e14 (k x y)
               have i₂ := b9e29
               grind)
            | exact superpose b9e29 b9e14
            | exact resolve b9e14 b9e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e29
          have b9e35 : y = (k x y) := by
            first
            | (have i₁ := b9e34
               have i₂ := b9e14 y
               grind)
            | exact superpose b9e14 b9e34
            | exact resolve b9e34 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e34
          have b9e52 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
          have b9e53 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
          clear b9e52
          have b9e54 : x = y ∨ (M.op x x) = (k x y) := by
            first
            | (have i₁ := b9e53
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e53
            | exact resolve b9e53 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e53
          have b9e56 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b9e54
               have r₂ := b9e26
               grind)
            | exact resolve b9e54 b9e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e54
          have b9e57 : y = (M.op x x) := by
            first
            | (have i₁ := b9e56
               have i₂ := b9e35
               grind)
            | exact superpose b9e35 b9e56
            | exact resolve b9e56 b9e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e35 b9e56
          have b9e58 : x = y := by
            first
            | (have i₁ := b9e57
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e57
            | exact resolve b9e57 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e57
          have b9e59 : False := by grind
          exact b9e59
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b10e25 : x ≠ (M.op x x) := by grind
            have b10e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e28 : False := by grind
            exact b10e28
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op x x) := by grind
            have b11e23 : y = (M.op y x) := by grind
            have b11e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e28 : (σ y) = (k (σ x) (σ y)) := by grind
            have b11e29 : (σ y) = (σ (k x y)) := by
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
            have b11e34 : (k x y) = (τ (σ y)) := by
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
            have b11e35 : y = (k x y) := by
              first
              | (have i₁ := b11e34
                 have i₂ := b11e15 y
                 grind)
              | exact superpose b11e15 b11e34
              | exact resolve b11e34 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e34
            have b11e60 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
            have b11e62 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
            clear b11e60
            have b11e63 : (M.op x x) = (k x y) := by
              first
              | (have r₁ := b11e62
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e62 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e62
            have b11e65 : y = (M.op x x) := by
              first
              | (have i₁ := b11e63
                 have i₂ := b11e35
                 grind)
              | exact superpose b11e35 b11e63
              | exact resolve b11e63 b11e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e35 b11e63
            have b11e66 : False := by grind
            exact b11e66
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b12e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e22 : y ≠ (M.op x x) := by grind
            have b12e23 : y = (M.op y x) := by grind
            have b12e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b12e25 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b12e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : x ≠ y := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e22
              | exact resolve b12e22 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (σ y)) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X0 (σ y) (σ x) X1
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e14
              | exact resolve b12e14 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e40 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 x X0 X1 x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e42 : ∀ X0 X1 : G, x = (M.op x (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e40 X0 X1
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e40
              | exact resolve b12e40 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e40
            have b12e47 : x = (M.op x y) := by
              first
              | (have i₁ := b12e42 y x
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e42
              | exact resolve b12e42 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e42
            have b12e59 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b12e18 (σ x) (σ y)
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e18
              | (have j0 := b12e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b12e18 (σ x) (σ y)
                 have r₂ := b12e25
                 grind)
              | exact resolve b12e18 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e60 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
              first
              | (have i₁ := b12e18 x y
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e18
              | (have j0 := b12e18 x y
                 grind)
              | (have r₁ := b12e18 x y
                 have r₂ := b12e23
                 grind)
              | exact resolve b12e18 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e61 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
            clear b12e60
            have b12e62 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
            clear b12e59
            have b12e64 : x = y ∨ (M.op x x) = (k x y) := by
              first
              | (have i₁ := b12e61
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e61
              | exact resolve b12e61 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e61
            have b12e65 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b12e62
                 have r₂ := b12e24
                 grind)
              | exact resolve b12e62 b12e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e62
            have b12e67 : (M.op x x) = (k x y) := by
              first
              | (have r₁ := b12e64
                 have r₂ := b12e28
                 grind)
              | exact resolve b12e64 b12e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28 b12e64
            have b12e68 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b12e65
                 have i₂ := b12e20 x y
                 grind)
              | exact superpose b12e20 b12e65
              | exact resolve b12e65 b12e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e65
            have b12e69 : x = (k x y) := by
              first
              | (have i₁ := b12e67
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e67
              | exact resolve b12e67 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e67
            have b12e178 : (M.op (σ x) (σ y)) = (M.op (σ (k x y)) (σ x)) := by
              first
              | (have i₁ := b12e34 (σ x) (σ x)
                 have i₂ := b12e68
                 grind)
              | exact superpose b12e68 b12e34
              | exact resolve b12e34 b12e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e34
            have b12e188 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b12e178
                 have i₂ := b12e69
                 grind)
              | exact superpose b12e69 b12e178
              | exact resolve b12e178 b12e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e178
            have b12e196 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b12e188
                 have i₂ := b12e68
                 grind)
              | exact superpose b12e68 b12e188
              | exact resolve b12e188 b12e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e68 b12e188
            have b12e200 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e196
                 have i₂ := b12e69
                 grind)
              | exact superpose b12e69 b12e196
              | exact resolve b12e196 b12e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e69 b12e196
            have b12e1227 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e200
                 grind)
              | exact superpose b12e200 b12e21
              | exact resolve b12e21 b12e200
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e200
            have b12e1256 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b12e1227
                 have i₂ := b12e47
                 grind)
              | exact superpose b12e47 b12e1227
              | exact resolve b12e1227 b12e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e47 b12e1227
            have b12e1257 : False := by grind
            exact b12e1257
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b13e27 : x ≠ (M.op x x) := by grind
              have b13e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : False := by grind
              exact b13e30
            · have b14e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e23 : y ≠ (M.op x x) := by grind
              have b14e24 : y = (M.op y x) := by grind
              have b14e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b14e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              have b14e28 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
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
              have b14e39 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (σ y)) := by
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
              have b14e41 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X0 X2 X3 (M.op x x)
                   have i₂ := b14e15 X0 x x X1
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e42 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op X4 X5)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X3)) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b14e15 (M.op X0 X3) X4 X5 X0
                   have i₂ := b14e15 X0 X1 X2 X3
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e45 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b14e15 X0 X1 X2 x
                   have i₂ := b14e15 X0 X3 X4 x
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e58 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b14e19 (σ x) (σ y)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e19
                | (have j0 := b14e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b14e19 (σ x) (σ y)
                   have r₂ := b14e26
                   grind)
                | exact resolve b14e19 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e59 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
                first
                | (have i₁ := b14e19 x y
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e19
                | (have j0 := b14e19 x y
                   grind)
                | (have r₁ := b14e19 x y
                   have r₂ := b14e24
                   grind)
                | exact resolve b14e19 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e61 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
              clear b14e59
              have b14e62 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
              clear b14e58
              have b14e63 : (M.op x x) = (k x y) := by
                first
                | (have r₁ := b14e61
                   have r₂ := b14e23
                   grind)
                | exact resolve b14e61 b14e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e61
              have b14e64 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b14e62
                   have r₂ := b14e25
                   grind)
                | exact resolve b14e62 b14e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e62
              have b14e66 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b14e64
                   have i₂ := b14e21 x y
                   grind)
                | exact superpose b14e21 b14e64
                | exact resolve b14e64 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e64
              have b14e67 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b14e66
                   have i₂ := b14e63
                   grind)
                | exact superpose b14e63 b14e66
                | exact resolve b14e66 b14e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e63 b14e66
              have b14e77 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X1 X2 X3 X1
                   have i₂ := b14e20 X1 X0
                   grind)
                | (have i₁ := b14e15 X0 X1 X2 X3
                   have i₂ := b14e20 X0 (M.op X0 X3)
                   grind)
                | exact superpose b14e20 b14e15
                | (have j1 := b14e20 X1 X0
                   grind)
                | exact resolve b14e15 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e91 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e16 (k X0 (τ X1))
                   have i₂ := b14e31 X1 X0
                   grind)
                | exact superpose b14e31 b14e16
                | exact resolve b14e16 b14e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e31
              have b14e96 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 (σ y)) (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e39 (M.op X0 X1) X0
                   have i₂ := b14e39 X0 X1
                   grind)
                | exact superpose b14e39 b14e39
                | exact resolve b14e39 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e102 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ y)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X0 X1 X2 x
                   have i₂ := b14e39 X0 x
                   grind)
                | exact superpose b14e39 b14e15
                | exact resolve b14e15 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e109 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e96 X0 X1
                   have i₂ := b14e102 (M.op X0 (σ y)) X0 X1
                   grind)
                | exact superpose b14e102 b14e96
                | exact resolve b14e96 b14e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e96
              have b14e120 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (σ (M.op x x))) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 (σ x) (σ x) X1
                   have i₂ := b14e67
                   grind)
                | exact superpose b14e67 b14e15
                | exact resolve b14e15 b14e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e121 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x x))) := by
                intro X0
                first
                | (have i₁ := b14e120 X0 x
                   have i₂ := b14e39 X0 x
                   grind)
                | exact superpose b14e39 b14e120
                | exact resolve b14e120 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e120
              have b14e252 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e45 X0 X1 X2 y x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e45
                | exact resolve b14e45 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e285 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b14e39 (M.op X0 X1) X2
                   have i₂ := b14e45 (M.op (M.op X0 X1) X2) X0 X1 X3 X4
                   grind)
                | (have i₁ := b14e39 (M.op X0 X1) X2
                   have i₂ := b14e45 (M.op (M.op X0 X1) X2) X3 X4 X0 X1
                   grind)
                | exact superpose b14e45 b14e39
                | exact resolve b14e39 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e45
              have b14e296 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op (M.op X0 X1) X2) (σ y)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e285 X0 X1 X2 x x
                   have i₂ := b14e102 (M.op (M.op X0 X1) X2) x x
                   grind)
                | exact superpose b14e102 b14e285
                | exact resolve b14e285 b14e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e285
              have b14e347 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e252 X0 (σ y) (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e252
                | exact resolve b14e252 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e348 : ∀ X0 : G, (M.op X0 (σ (M.op x x))) = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e252 X0 (σ x) (σ x)
                   have i₂ := b14e67
                   grind)
                | exact superpose b14e67 b14e252
                | exact resolve b14e252 b14e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e361 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 y) := by
                intro X0 X3
                first
                | (have i₁ := b14e15 X0 x x X3
                   have i₂ := b14e252 X0 x x
                   grind)
                | exact superpose b14e252 b14e15
                | exact resolve b14e15 b14e252
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e252
              have b14e428 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e347 (σ x)
                   grind)
                | exact superpose b14e347 b14e22
                | exact resolve b14e22 b14e347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e494 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X0 (σ y)) (M.op X0 X1)) (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e41 (M.op X0 X1) X0 X2 X3
                   have i₂ := b14e39 X0 X1
                   grind)
                | exact superpose b14e39 b14e41
                | exact resolve b14e41 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e41
              have b14e577 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X0 (σ y)) (M.op X0 X1)) (σ y)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e494 X0 X1 X2 X3
                   have i₂ := b14e102 (M.op (M.op X0 (σ y)) (M.op X0 X1)) X0 X1
                   grind)
                | exact superpose b14e102 b14e494
                | exact resolve b14e494 b14e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e494
              have b14e610 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e577 X0 X1 X2 X3
                   have i₂ := b14e109 (M.op X0 (σ y)) (M.op X0 X1)
                   grind)
                | exact superpose b14e109 b14e577
                | exact resolve b14e577 b14e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e577
              have b14e632 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 (σ y)) (σ y)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e610 X0 X1 X2 X3
                   have i₂ := b14e296 X0 (σ y) (σ y)
                   grind)
                | exact superpose b14e296 b14e610
                | exact resolve b14e610 b14e296
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e296 b14e610
              have b14e649 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 (σ y)) y) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e632 X0 X1 X2 X3
                   have i₂ := b14e347 (M.op X0 (σ y))
                   grind)
                | exact superpose b14e347 b14e632
                | exact resolve b14e632 b14e347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e632
              have b14e658 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 y) y) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e649 X0 X1 X2 X3
                   have i₂ := b14e347 X0
                   grind)
                | exact superpose b14e347 b14e649
                | exact resolve b14e649 b14e347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e649
              have b14e663 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 y) y) := by
                intro X0 X1
                first
                | (have i₁ := b14e658 X0 X1 x x
                   have i₂ := b14e102 (M.op X0 X1) x x
                   grind)
                | exact superpose b14e102 b14e658
                | exact resolve b14e658 b14e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e658
              have b14e667 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 y) y) := by
                intro X0 X1
                first
                | (have i₁ := b14e663 X0 X1
                   have i₂ := b14e347 (M.op X0 X1)
                   grind)
                | exact superpose b14e347 b14e663
                | exact resolve b14e663 b14e347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e663
              have b14e685 : (M.op (σ (M.op x x)) (σ x)) = (M.op (σ x) y) := by
                first
                | (have i₁ := b14e361 (σ x) (σ x)
                   have i₂ := b14e67
                   grind)
                | exact superpose b14e67 b14e361
                | exact resolve b14e361 b14e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e866 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X3)) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b14e20 (M.op X0 X3) X4
                   have i₂ := b14e42 X0 X1 X2 X3 X0 X3
                   grind)
                | (have i₁ := b14e20 (M.op X0 (M.op X1 X2)) X1
                   have i₂ := b14e42 X0 X1 X2 (M.op X1 X2) X4 x
                   grind)
                | exact superpose b14e42 b14e20
                | (have j0 := b14e20 (M.op X0 X3) X4
                   grind)
                | exact resolve b14e20 b14e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e42
              have b14e925 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (σ y)) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b14e866 X0 X1 X2 X3 X4
                   have i₂ := b14e102 (M.op X0 (M.op X1 X2)) X0 X3
                   grind)
                | exact superpose b14e102 b14e866
                | (have j0 := b14e866 X0 X1 X2 X3 X4
                   grind)
                | exact resolve b14e866 b14e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e866
              have b14e994 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (σ y)) (σ y)) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
                intro X0 X3 X4
                first
                | (have i₁ := b14e925 X0 x x X3 X4
                   have i₂ := b14e109 X0 (M.op x x)
                   grind)
                | exact superpose b14e109 b14e925
                | (have j0 := b14e925 X0 x x X3 X4
                   grind)
                | exact resolve b14e925 b14e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e109 b14e925
              have b14e1063 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (σ y)) y) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
                intro X0 X3 X4
                first
                | (have i₁ := b14e994 X0 X3 X4
                   have i₂ := b14e347 (M.op X0 (σ y))
                   grind)
                | exact superpose b14e347 b14e994
                | (have j0 := b14e994 X0 X3 X4
                   grind)
                | exact resolve b14e994 b14e347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e994
              have b14e1130 : ∀ X0 X3 X4 : G, (M.op (M.op X0 y) y) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
                intro X0 X3 X4
                first
                | (have i₁ := b14e1063 X0 X3 X4
                   have i₂ := b14e667 X0 (σ y)
                   grind)
                | exact superpose b14e667 b14e1063
                | (have j0 := b14e1063 X0 X3 X4
                   grind)
                | exact resolve b14e1063 b14e667
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1063
              have b14e1190 : ∀ X0 X3 X4 : G, (M.op X4 (σ y)) = X4 ∨ (M.op (M.op X0 y) y) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) := by
                intro X0 X3 X4
                first
                | (have i₁ := b14e1130 X0 X3 X4
                   have i₂ := b14e102 X4 X0 X3
                   grind)
                | exact superpose b14e102 b14e1130
                | (have j0 := b14e1130 X0 X3 X4
                   grind)
                | exact resolve b14e1130 b14e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1130
              have b14e1236 : ∀ X0 X3 X4 : G, (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op (M.op X0 y) y) = X4 ∨ (M.op X4 y) = X4 := by
                intro X0 X3 X4
                first
                | (have i₁ := b14e1190 X0 X3 X4
                   have i₂ := b14e347 X4
                   grind)
                | exact superpose b14e347 b14e1190
                | (have j0 := b14e1190 X0 X3 X4
                   grind)
                | exact resolve b14e1190 b14e347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1190
              have b14e1804 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have j0 := b14e77 X0 X1 X2 X3
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e77
              have b14e1806 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e1804 X0 X1 x x
                   have i₂ := b14e102 X1 x x
                   grind)
                | exact superpose b14e102 b14e1804
                | (have j0 := b14e1804 X0 X1 x x
                   grind)
                | (have r₁ := b14e1804 (M.op X0 (σ y)) X0 X1 x
                   have r₂ := b14e102 X0 X1 x
                   grind)
                | exact resolve b14e1804 b14e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1804
              have b14e1880 : ∀ X0 X1 : G, (M.op X1 y) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e1806 X0 X1
                   have i₂ := b14e347 X1
                   grind)
                | exact superpose b14e347 b14e1806
                | (have j0 := b14e1806 X0 X1
                   grind)
                | (have r₁ := b14e1806 (M.op X0 y) X0
                   have r₂ := b14e347 X0
                   grind)
                | exact resolve b14e1806 b14e347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1806
              have b14e2381 : ∀ X0 : G, (M.op (σ (M.op x x)) y) = X0 ∨ (k (σ (M.op x x)) X0) = (M.op (σ (M.op x x)) X0) ∨ (M.op X0 (σ (M.op x x))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e20 (σ (M.op x x)) X0
                   have i₂ := b14e348 (σ (M.op x x))
                   grind)
                | exact superpose b14e348 b14e20
                | (have j0 := b14e20 (σ (M.op x x)) X0
                   grind)
                | exact resolve b14e20 b14e348
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e348
              have b14e2423 : ∀ X0 : G, (k (σ (M.op x x)) X0) = (M.op (σ (M.op x x)) X0) ∨ (M.op X0 (σ (M.op x x))) = X0 := by
                intro X0
                first
                | (have j0 := b14e2381 X0
                   have j1 := b14e1880 X0 (σ (M.op x x))
                   grind)
                | (have r₁ := b14e2381 X0
                   have r₂ := b14e1880 X0 (σ (M.op x x))
                   grind)
                | (have r₁ := b14e2381 (M.op x y)
                   have r₂ := b14e1880 (M.op (σ (M.op x x)) y) x
                   grind)
                | (have r₁ := b14e2381 y
                   have r₂ := b14e1880 (k (σ (M.op x x)) y) (σ (M.op x x))
                   grind)
                | exact resolve b14e2381 b14e1880
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e2381
              have b14e2440 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (k (σ (M.op x x)) X0) = (M.op (σ (M.op x x)) X0) := by
                intro X0
                first
                | (have i₁ := b14e2423 X0
                   have i₂ := b14e121 X0
                   grind)
                | exact superpose b14e121 b14e2423
                | (have j0 := b14e2423 X0
                   grind)
                | exact resolve b14e2423 b14e121
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e121 b14e2423
              have b14e2455 : ∀ X0 : G, (k (σ (M.op x x)) X0) = (M.op (σ (M.op x x)) X0) ∨ (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b14e2440 X0
                   have i₂ := b14e347 X0
                   grind)
                | exact superpose b14e347 b14e2440
                | (have j0 := b14e2440 X0
                   grind)
                | exact resolve b14e2440 b14e347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e2440
              have b14e7522 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) y) ≠ X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e1880 X2 (M.op X0 X1)
                   have i₂ := b14e667 X0 X1
                   grind)
                | (have i₁ := b14e1880 X0 (M.op X0 y)
                   have i₂ := b14e667 X0 X1
                   grind)
                | exact superpose b14e667 b14e1880
                | (have j0 := b14e1880 X2 (M.op X0 X1)
                   grind)
                | (have r₁ := b14e1880 (M.op (M.op X0 y) y) (M.op X0 X1)
                   have r₂ := b14e667 X0 X1
                   grind)
                | (have r₁ := b14e1880 (M.op (M.op X0 X1) y) (M.op X0 y)
                   have r₂ := b14e667 X0 X1
                   grind)
                | exact resolve b14e1880 b14e667
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e667 b14e1880
              have b14e7552 : ∀ X0 X1 X2 : G, (M.op X2 (σ y)) = X2 ∨ (M.op (M.op X0 y) y) ≠ X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e7522 X0 X1 X2
                   have i₂ := b14e102 X2 X0 X1
                   grind)
                | exact superpose b14e102 b14e7522
                | (have j0 := b14e7522 X0 X1 X2
                   grind)
                | exact resolve b14e7522 b14e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e102 b14e7522
              have b14e7570 : ∀ X0 X1 X2 : G, (M.op X2 y) = X2 ∨ (M.op (M.op X0 y) y) ≠ X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e7552 X0 X1 X2
                   have i₂ := b14e347 X2
                   grind)
                | exact superpose b14e347 b14e7552
                | (have j0 := b14e7552 X0 X1 X2
                   grind)
                | (have r₁ := b14e7552 X0 X1 (M.op (M.op X0 y) (σ y))
                   have r₂ := b14e347 (M.op X0 y)
                   grind)
                | exact resolve b14e7552 b14e347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7552
              have b14e7580 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 y) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b14e7570 X0 X1 X2
                   have j1 := b14e1236 X0 X1 X2
                   grind)
                | (have r₁ := b14e7570 X0 X1 (k (M.op X0 y) y)
                   have r₂ := b14e1236 X0 y y
                   grind)
                | (have r₁ := b14e7570 X0 X1 x
                   have r₂ := b14e1236 X0 x x
                   grind)
                | (have r₁ := b14e7570 X0 X1 (M.op (M.op X0 y) y)
                   have r₂ := b14e1236 X0 x (M.op (M.op X0 y) y)
                   grind)
                | exact resolve b14e7570 b14e1236
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1236 b14e7570
              have b14e111303 : ∀ X0 : G, (k (M.op x x) (τ X0)) = (τ (M.op (σ (M.op x x)) X0)) ∨ (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b14e91 (M.op x x) X0
                   have i₂ := b14e2455 X0
                   grind)
                | exact superpose b14e2455 b14e91
                | (have j1 := b14e2455 X0
                   grind)
                | exact resolve b14e91 b14e2455
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e91 b14e2455
              have b14e151992 : (τ (M.op (σ x) y)) = (k (M.op x x) (τ (σ x))) ∨ (σ x) = (M.op (σ x) y) := by
                first
                | (have i₁ := b14e111303 (σ x)
                   have i₂ := b14e685
                   grind)
                | exact superpose b14e685 b14e111303
                | (have j0 := b14e111303 (σ x)
                   grind)
                | exact resolve b14e111303 b14e685
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e685 b14e111303
              have b14e152054 : (k (M.op x x) x) = (τ (M.op (σ x) y)) ∨ (σ x) = (M.op (σ x) y) := by
                first
                | (have i₁ := b14e151992
                   have i₂ := b14e16 x
                   grind)
                | exact superpose b14e16 b14e151992
                | exact resolve b14e151992 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e151992
              have b14e152180 : (M.op (σ x) y) = (σ (k (M.op x x) x)) ∨ (σ x) = (M.op (σ x) y) := by
                first
                | (have i₁ := b14e17 (M.op (σ x) y)
                   have i₂ := b14e152054
                   grind)
                | exact superpose b14e152054 b14e17
                | exact resolve b14e17 b14e152054
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e152054
              have b14e152647 : (M.op (σ x) y) = (σ (M.op (M.op x x) x)) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b14e152180
                   have i₂ := b14e7580 x x x
                   grind)
                | exact superpose b14e7580 b14e152180
                | (have j1 := b14e7580 x x (σ x)
                   grind)
                | exact resolve b14e152180 b14e7580
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7580 b14e152180
              have b14e152697 : (M.op (σ x) y) = (σ (M.op x (σ y))) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b14e152647
                   have i₂ := b14e39 x x
                   grind)
                | exact superpose b14e39 b14e152647
                | exact resolve b14e152647 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e39 b14e152647
              have b14e152712 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b14e152697
                   have i₂ := b14e347 x
                   grind)
                | exact superpose b14e347 b14e152697
                | exact resolve b14e152697 b14e347
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e347 b14e152697
              have b14e152727 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b14e152712
                   have r₂ := b14e428
                   grind)
                | exact resolve b14e152712 b14e428
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e428 b14e152712
              have b14e153490 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b14e361 (σ x) y
                   have i₂ := b14e152727
                   grind)
                | exact superpose b14e152727 b14e361
                | exact resolve b14e361 b14e152727
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e152727
              have b14e153552 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b14e153490
                   have i₂ := b14e67
                   grind)
                | exact superpose b14e67 b14e153490
                | exact resolve b14e153490 b14e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e67 b14e153490
              have b14e154349 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b14e16 (M.op x x)
                   have i₂ := b14e153552
                   grind)
                | exact superpose b14e153552 b14e16
                | exact resolve b14e16 b14e153552
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e153552
              have b14e154442 : x = (M.op x x) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b14e154349
                   have i₂ := b14e16 x
                   grind)
                | exact superpose b14e16 b14e154349
                | exact resolve b14e154349 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e154349
              have b14e154452 : x = (M.op x y) := by
                first
                | (have r₁ := b14e154442
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e154442 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e154442
              have b14e154664 : x = (M.op x x) := by
                first
                | (have i₁ := b14e361 x y
                   have i₂ := b14e154452
                   grind)
                | exact superpose b14e154452 b14e361
                | exact resolve b14e361 b14e154452
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e361 b14e154452
              have b14e154777 : False := by grind
              exact b14e154777
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b15e22 : y ≠ (M.op x x) := by grind
            have b15e23 : y = (M.op y x) := by grind
            have b15e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e28 : x ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e22
              | exact resolve b15e22 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e36 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 x X0 X1 x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e14
              | exact resolve b15e14 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e40 : ∀ X0 X1 : G, x = (M.op x (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e36 X0 X1
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e36
              | exact resolve b15e36 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e36
            have b15e41 : x = (M.op x y) := by
              first
              | (have i₁ := b15e40 y x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e40
              | exact resolve b15e40 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e40
            have b15e53 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
            have b15e58 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
            clear b15e53
            have b15e60 : x = y ∨ (M.op x x) = (k x y) := by
              first
              | (have i₁ := b15e58
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e58
              | exact resolve b15e58 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e58
            have b15e61 : (M.op x x) = (k x y) := by
              first
              | (have r₁ := b15e60
                 have r₂ := b15e28
                 grind)
              | exact resolve b15e60 b15e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28 b15e60
            have b15e62 : x = (k x y) := by
              first
              | (have i₁ := b15e61
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e61
              | exact resolve b15e61 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e61
            have b15e75 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
            have b15e1170 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b15e75 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e75
            have b15e1171 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b15e1170
                 have r₂ := b15e25
                 grind)
              | exact resolve b15e1170 b15e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1170
            have b15e1172 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b15e1171
                 have i₂ := b15e20 x y
                 grind)
              | exact superpose b15e20 b15e1171
              | exact resolve b15e1171 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1171
            have b15e1173 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e1172
                 have i₂ := b15e62
                 grind)
              | exact superpose b15e62 b15e1172
              | exact resolve b15e1172 b15e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e62 b15e1172
            have b15e1174 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b15e21
                 have i₂ := b15e1173
                 grind)
              | exact superpose b15e1173 b15e21
              | exact resolve b15e21 b15e1173
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1173
            have b15e1202 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b15e1174
                 have i₂ := b15e41
                 grind)
              | exact superpose b15e41 b15e1174
              | exact resolve b15e1174 b15e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e41 b15e1174
            have b15e1203 : False := by grind
            exact b15e1203
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b16e27 : x ≠ (M.op x x) := by grind
              have b16e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e30 : False := by grind
              exact b16e30
            · have b17e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b17e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b17e23 : y ≠ (M.op x x) := by grind
              have b17e24 : y = (M.op y x) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b17e28 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
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
              have b17e39 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X4) X0) := by
                intro X0 X1 X4
                first
                | (have i₁ := b17e15 X0 x x X4
                   have i₂ := b17e15 X0 x x X1
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e40 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y y) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 y X0 X1 x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e41 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 X0 X2 X3 (M.op x x)
                   have i₂ := b17e15 X0 x x X1
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e42 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op X4 X5)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X3)) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b17e15 (M.op X0 X3) X4 X5 X0
                   have i₂ := b17e15 X0 X1 X2 X3
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e43 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b17e15 X0 X1 X2 x
                   have i₂ := b17e15 X0 X3 X4 x
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e48 : ∀ X2 : G, (M.op y y) = (M.op (M.op y X2) y) := by
                intro X2
                first
                | (have i₁ := b17e15 y x x X2
                   have i₂ := b17e40 x x
                   grind)
                | exact superpose b17e40 b17e15
                | exact resolve b17e15 b17e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e40
              have b17e51 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
              have b17e55 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
              clear b17e51
              have b17e56 : (M.op x x) = (k x y) := by
                first
                | (have r₁ := b17e55
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e55 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e55
              have b17e63 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e66 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 X1 X2 X3 X1
                   have i₂ := b17e20 X1 X0
                   grind)
                | (have i₁ := b17e15 X0 X1 X2 X3
                   have i₂ := b17e20 X0 (M.op X0 X3)
                   grind)
                | exact superpose b17e20 b17e15
                | (have j1 := b17e20 X1 X0
                   grind)
                | exact resolve b17e15 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e68 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
              have b17e164 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e43 X0 X1 X2 y x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e43
                | exact resolve b17e43 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e43
              have b17e229 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 y) := by
                intro X0 X3
                first
                | (have i₁ := b17e15 X0 x x X3
                   have i₂ := b17e164 X0 x x
                   grind)
                | exact superpose b17e164 b17e15
                | exact resolve b17e15 b17e164
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e234 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) y) = (M.op (M.op X0 X1) (M.op X3 X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b17e15 (M.op X0 X1) X3 X4 X2
                   have i₂ := b17e164 (M.op (M.op X0 X1) X2) X0 X1
                   grind)
                | exact superpose b17e164 b17e15
                | exact resolve b17e15 b17e164
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e245 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op (M.op (M.op X0 X1) X2) y) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e234 X0 X1 X2 x x
                   have i₂ := b17e164 (M.op X0 X1) x x
                   grind)
                | exact superpose b17e164 b17e234
                | exact resolve b17e234 b17e164
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e234
              have b17e317 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 X3) X0)) = (M.op (M.op (M.op (M.op X0 X3) X0) X4) (M.op (M.op X0 X3) X0)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b17e39 (M.op (M.op X0 X3) X0) X4 X0
                   have i₂ := b17e41 X0 X3 X1 X2
                   grind)
                | exact superpose b17e41 b17e39
                | exact resolve b17e39 b17e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e39 b17e41
              have b17e328 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 X3) X0)) = (M.op (M.op (M.op X0 X3) X0) y) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e317 X0 X1 X2 X3 x
                   have i₂ := b17e229 (M.op (M.op X0 X3) X0) x
                   grind)
                | exact superpose b17e229 b17e317
                | exact resolve b17e317 b17e229
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e317
              have b17e360 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 X3) X0)) = (M.op (M.op X0 X3) y) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e328 X0 X1 X2 X3
                   have i₂ := b17e245 X0 X3 X0
                   grind)
                | exact superpose b17e245 b17e328
                | exact resolve b17e328 b17e245
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e245 b17e328
              have b17e379 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) y) = (M.op (M.op X0 X3) y) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e360 X0 X1 X2 X3
                   have i₂ := b17e164 (M.op X0 (M.op X1 X2)) (M.op X0 X3) X0
                   grind)
                | exact superpose b17e164 b17e360
                | exact resolve b17e360 b17e164
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e360
              have b17e393 : ∀ X0 X3 : G, (M.op (M.op X0 X3) y) = (M.op (M.op X0 y) y) := by
                intro X0 X3
                first
                | (have i₁ := b17e379 X0 x x X3
                   have i₂ := b17e164 X0 x x
                   grind)
                | exact superpose b17e164 b17e379
                | exact resolve b17e379 b17e164
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e379
              have b17e545 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 X3)) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b17e20 (M.op X0 X3) X4
                   have i₂ := b17e42 X0 X1 X2 X3 X0 X3
                   grind)
                | (have i₁ := b17e20 (M.op X0 (M.op X1 X2)) X1
                   have i₂ := b17e42 X0 X1 X2 (M.op X1 X2) X4 x
                   grind)
                | exact superpose b17e42 b17e20
                | (have j0 := b17e20 (M.op X0 X3) X4
                   grind)
                | exact resolve b17e20 b17e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e42
              have b17e596 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) y) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b17e545 X0 X1 X2 X3 X4
                   have i₂ := b17e164 (M.op X0 (M.op X1 X2)) X0 X3
                   grind)
                | exact superpose b17e164 b17e545
                | (have j0 := b17e545 X0 X1 X2 X3 X4
                   grind)
                | exact resolve b17e545 b17e164
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e545
              have b17e652 : ∀ X0 X3 X4 : G, (M.op (M.op X0 y) y) = X4 ∨ (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op X4 (M.op X0 X3)) = X4 := by
                intro X0 X3 X4
                first
                | (have i₁ := b17e596 X0 x x X3 X4
                   have i₂ := b17e393 X0 (M.op x x)
                   grind)
                | exact superpose b17e393 b17e596
                | (have j0 := b17e596 X0 x x X3 X4
                   grind)
                | exact resolve b17e596 b17e393
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e393 b17e596
              have b17e702 : ∀ X0 X3 X4 : G, (M.op (M.op X0 X3) X4) = (k (M.op X0 X3) X4) ∨ (M.op (M.op X0 y) y) = X4 ∨ (M.op X4 y) = X4 := by
                intro X0 X3 X4
                first
                | (have i₁ := b17e652 X0 X3 X4
                   have i₂ := b17e164 X4 X0 X3
                   grind)
                | exact superpose b17e164 b17e652
                | (have j0 := b17e652 X0 X3 X4
                   grind)
                | exact resolve b17e652 b17e164
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e652
              have b17e772 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e63 (σ X1) (σ X0)
                   have i₂ := b17e21 X0 X1
                   grind)
                | exact superpose b17e21 b17e63
                | (have j0 := b17e63 (σ X1) (σ X0)
                   grind)
                | exact resolve b17e63 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e63
              have b17e913 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b17e68 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e68
              have b17e914 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e913
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e913 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e913
              have b17e915 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e914
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e914
                | exact resolve b17e914 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e914
              have b17e916 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b17e915
                   have i₂ := b17e56
                   grind)
                | exact superpose b17e56 b17e915
                | exact resolve b17e915 b17e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e56 b17e915
              have b17e917 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b17e22
                   have i₂ := b17e916
                   grind)
                | exact superpose b17e916 b17e22
                | exact resolve b17e22 b17e916
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e1084 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have j0 := b17e66 X0 X1 X2 X3
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e66
              have b17e1086 : ∀ X0 X1 : G, (M.op X1 y) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b17e1084 X0 X1 x x
                   have i₂ := b17e164 X1 x x
                   grind)
                | exact superpose b17e164 b17e1084
                | (have j0 := b17e1084 X0 X1 x x
                   grind)
                | (have r₁ := b17e1084 (M.op X0 y) X0 X1 x
                   have r₂ := b17e164 X0 X1 x
                   grind)
                | exact resolve b17e1084 b17e164
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e164 b17e1084
              have b17e17044 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op (M.op y y) y) = X0 ∨ (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b17e702 y x x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e702
                | (have j0 := b17e702 y x X0
                   grind)
                | exact resolve b17e702 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e702
              have b17e17090 : ∀ X0 : G, (M.op y y) = X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b17e17044 X0
                   have i₂ := b17e48 y
                   grind)
                | exact superpose b17e48 b17e17044
                | (have j0 := b17e17044 X0
                   grind)
                | exact resolve b17e17044 b17e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e48 b17e17044
              have b17e17091 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
                intro X0
                first
                | (have j0 := b17e17090 X0
                   have j1 := b17e1086 X0 y
                   grind)
                | (have r₁ := b17e17090 X0
                   have r₂ := b17e1086 X0 y
                   grind)
                | (have r₁ := b17e17090 (M.op x y)
                   have r₂ := b17e1086 (M.op y y) x
                   grind)
                | (have r₁ := b17e17090 y
                   have r₂ := b17e1086 (k y y) y
                   grind)
                | exact resolve b17e17090 b17e1086
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1086 b17e17090
              have b17e17112 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = (M.op (τ X0) y) := by
                intro X0
                first
                | (have i₁ := b17e31 X0 y
                   have i₂ := b17e17091 (τ X0)
                   grind)
                | exact superpose b17e17091 b17e31
                | (have j1 := b17e17091 (τ X0)
                   grind)
                | exact resolve b17e31 b17e17091
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e31 b17e17091
              have b17e23295 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e772 y x
                   grind)
                | exact superpose b17e772 b17e26
                | (have j1 := b17e772 y x
                   grind)
                | (have r₁ := b17e26
                   have r₂ := b17e772 x y
                   grind)
                | exact resolve b17e26 b17e772
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e772
              have b17e23536 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b17e23295
                   have i₂ := b17e916
                   grind)
                | exact superpose b17e916 b17e23295
                | exact resolve b17e23295 b17e916
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e916 b17e23295
              have b17e33984 : ∀ X0 : G, (σ (M.op y X0)) = (k (σ y) (σ X0)) ∨ (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b17e17112 (σ X0)
                   have i₂ := b17e16 X0
                   grind)
                | exact superpose b17e16 b17e17112
                | exact resolve b17e17112 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e17112
              have b17e34056 : ∀ X0 : G, (σ (M.op y X0)) = (σ (k y X0)) ∨ (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b17e33984 X0
                   have i₂ := b17e21 y X0
                   grind)
                | exact superpose b17e21 b17e33984
                | (have j0 := b17e33984 X0
                   grind)
                | exact resolve b17e33984 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e33984
              have b17e130024 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y x)) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b17e23536
                   have i₂ := b17e34056 x
                   grind)
                | exact superpose b17e34056 b17e23536
                | (have j1 := b17e34056 x
                   grind)
                | exact resolve b17e23536 b17e34056
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e23536 b17e34056
              have b17e130034 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y x)) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b17e130024
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e130024
                | exact resolve b17e130024 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e130024
              have b17e130035 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y x)) ∨ x = (M.op x y) := by grind
              clear b17e130034
              have b17e130054 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b17e130035
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e130035
                | exact resolve b17e130035 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e130035
              have b17e130290 : (M.op x x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b17e16 (M.op x x)
                   have i₂ := b17e130054
                   grind)
                | exact superpose b17e130054 b17e16
                | exact resolve b17e16 b17e130054
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e130054
              have b17e130337 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b17e130290
                   have i₂ := b17e16 x
                   grind)
                | exact superpose b17e16 b17e130290
                | exact resolve b17e130290 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e130290
              have b17e130344 : x = (M.op x y) ∨ (σ x) = (σ y) := by
                first
                | (have r₁ := b17e130337
                   have r₂ := b17e28
                   grind)
                | exact resolve b17e130337 b17e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e130337
              have b17e130437 : x = (M.op x x) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b17e229 x y
                   have i₂ := b17e130344
                   grind)
                | exact superpose b17e130344 b17e229
                | exact resolve b17e229 b17e130344
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e229 b17e130344
              have b17e130485 : (σ x) = (σ y) := by
                first
                | (have r₁ := b17e130437
                   have r₂ := b17e28
                   grind)
                | exact resolve b17e130437 b17e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e130437
              have b17e130551 : y = (τ (σ x)) := by
                first
                | (have i₁ := b17e16 y
                   have i₂ := b17e130485
                   grind)
                | exact superpose b17e130485 b17e16
                | exact resolve b17e16 b17e130485
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e130485
              have b17e130678 : x = y := by
                first
                | (have i₁ := b17e130551
                   have i₂ := b17e16 x
                   grind)
                | exact superpose b17e16 b17e130551
                | exact resolve b17e130551 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e130551
              have b17e130884 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b17e917
                   have i₂ := b17e130678
                   grind)
                | exact superpose b17e130678 b17e917
                | exact resolve b17e917 b17e130678
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e917 b17e130678
              have b17e130997 : False := by grind
              exact b17e130997
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : y ≠ (M.op x x) := by grind
          have b18e22 : y ≠ (M.op y x) := by grind
          have b18e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b18e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e26 : x ≠ y := by
            first
            | (have i₁ := b18e21
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e21
            | exact resolve b18e21 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e28 : (σ y) = (k (σ x) (σ y)) := by grind
          have b18e29 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b18e28
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e28
            | exact resolve b18e28 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e28
          have b18e34 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b18e14 (k x y)
               have i₂ := b18e29
               grind)
            | exact superpose b18e29 b18e14
            | exact resolve b18e14 b18e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e29
          have b18e35 : y = (k x y) := by
            first
            | (have i₁ := b18e34
               have i₂ := b18e14 y
               grind)
            | exact superpose b18e14 b18e34
            | exact resolve b18e34 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e34
          have b18e45 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 x X0 X1 x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e47 : ∀ X0 X1 : G, x = (M.op x (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e45 X0 X1
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e45
            | exact resolve b18e45 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e45
          have b18e73 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b18e35
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e35
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e35 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e35
          have b18e85 : y = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b18e73
               have r₂ := b18e22
               grind)
            | exact resolve b18e73 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e73
          have b18e88 : x = y ∨ y = (M.op x y) := by
            first
            | (have i₁ := b18e85
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e85
            | exact resolve b18e85 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e85
          have b18e91 : y = (M.op x y) := by
            first
            | (have r₁ := b18e88
               have r₂ := b18e26
               grind)
            | exact resolve b18e88 b18e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e88
          have b18e93 : x = (M.op x y) := by
            first
            | (have i₁ := b18e47 x y
               have i₂ := b18e91
               grind)
            | exact superpose b18e91 b18e47
            | exact resolve b18e47 b18e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e47
          have b18e104 : x = y := by
            first
            | (have i₁ := b18e91
               have i₂ := b18e93
               grind)
            | exact superpose b18e93 b18e91
            | exact resolve b18e91 b18e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e91 b18e93
          have b18e110 : False := by grind
          exact b18e110
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b19e25 : x ≠ (M.op x x) := by grind
            have b19e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e28 : False := by grind
            exact b19e28
          · have b20e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op x x) := by grind
            have b20e23 : y ≠ (M.op y x) := by grind
            have b20e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : (σ y) = (k (σ x) (σ y)) := by grind
            have b20e29 : (σ y) = (σ (k x y)) := by
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
            have b20e34 : (k x y) = (τ (σ y)) := by
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
            have b20e35 : y = (k x y) := by
              first
              | (have i₁ := b20e34
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e34
              | exact resolve b20e34 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e34
            have b20e70 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b20e35
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e35
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e35 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35
            have b20e79 : y = (M.op x y) ∨ y = (M.op y x) := by
              first
              | (have r₁ := b20e70
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e70 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e70
            have b20e82 : y = (M.op x y) := by
              first
              | (have r₁ := b20e79
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e79 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e79
            have b20e85 : ∀ X0 X1 : G, (M.op y x) = (M.op x (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b20e14 x X0 X1 y
                 have i₂ := b20e82
                 grind)
              | exact superpose b20e82 b20e14
              | exact resolve b20e14 b20e82
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e312 : (M.op x y) = (M.op y x) := by
              first
              | (have i₁ := b20e85 x y
                 have i₂ := b20e82
                 grind)
              | exact superpose b20e82 b20e85
              | exact resolve b20e85 b20e82
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e85
            have b20e336 : y = (M.op y x) := by
              first
              | (have i₁ := b20e312
                 have i₂ := b20e82
                 grind)
              | exact superpose b20e82 b20e312
              | exact resolve b20e312 b20e82
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e82 b20e312
            have b20e340 : False := by grind
            exact b20e340
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X0) := by
              intro X0 X1 X2 X3
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b21e22 : y ≠ (M.op x x) := by grind
            have b21e23 : y ≠ (M.op y x) := by grind
            have b21e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b21e25 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b21e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e28 : x ≠ y := by
              first
              | (have i₁ := b21e22
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e22
              | exact resolve b21e22 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e29 : x = (k x x) := by grind
            have b21e34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (σ y)) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X0 (σ y) (σ x) X1
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e14
              | exact resolve b21e14 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e39 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 x X0 X1 x
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e41 : ∀ X0 X1 : G, x = (M.op x (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e39 X0 X1
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e39
              | exact resolve b21e39 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e39
            have b21e44 : x = (M.op x (σ y)) := by
              first
              | (have i₁ := b21e41 (σ y) (σ x)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e41
              | exact resolve b21e41 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e50 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 x) := by
              intro X0 X3
              first
              | (have i₁ := b21e14 X0 x (M.op x x) X3
                 have i₂ := b21e41 x x
                 grind)
              | exact superpose b21e41 b21e14
              | exact resolve b21e14 b21e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e56 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
            have b21e59 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
            clear b21e56
            have b21e60 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e59
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e59 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e59
            have b21e62 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b21e60
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e60
              | exact resolve b21e60 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e60
            have b21e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
            have b21e90 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 x) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e14 X0 X1 X2 x
                 have i₂ := b21e50 X0 x
                 grind)
              | exact superpose b21e50 b21e14
              | exact resolve b21e14 b21e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e50
            have b21e111 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b21e90 X0 (σ y) (σ x)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e90
              | exact resolve b21e90 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e147 : (σ (M.op x y)) ≠ (M.op (σ x) x) := by
              first
              | (have i₁ := b21e21
                 have i₂ := b21e111 (σ x)
                 grind)
              | exact superpose b21e111 b21e21
              | exact resolve b21e21 b21e111
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e111
            have b21e219 : (σ (k x y)) = (k (σ x) (σ (k x y))) := by grind
            have b21e226 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (k x y))) := by
              intro X0
              first
              | (have i₁ := b21e90 X0 (σ x) (σ x)
                 have i₂ := b21e62
                 grind)
              | exact superpose b21e62 b21e90
              | exact resolve b21e90 b21e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e90
            have b21e231 : (σ (k x y)) = (σ (k x (k x y))) := by
              first
              | (have i₁ := b21e219
                 have i₂ := b21e20 x (k x y)
                 grind)
              | exact superpose b21e20 b21e219
              | exact resolve b21e219 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e219
            have b21e1323 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
              intro X0
              first
              | (have i₁ := b21e226 X0
                 have i₂ := b21e19 x y
                 grind)
              | exact superpose b21e19 b21e226
              | (have j1 := b21e19 x y
                 grind)
              | exact resolve b21e226 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e226
            have b21e1374 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x x) := by
              intro X0
              first
              | (have j0 := b21e1323 X0
                 grind)
              | (have r₁ := b21e1323 X0
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e1323 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1323
            have b21e1390 : ∀ X0 : G, x = y ∨ (M.op X0 x) = (M.op X0 (σ (M.op x y))) := by
              intro X0
              first
              | (have i₁ := b21e1374 X0
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e1374
              | (have j0 := b21e1374 X0
                 grind)
              | exact resolve b21e1374 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1374
            have b21e1399 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (M.op x y))) := by
              intro X0
              first
              | (have j0 := b21e1390 X0
                 grind)
              | (have r₁ := b21e1390 X0
                 have r₂ := b21e28
                 grind)
              | exact resolve b21e1390 b21e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1390
            have b21e1676 : (k x (k x y)) = (τ (σ (k x y))) := by
              first
              | (have i₁ := b21e15 (k x (k x y))
                 have i₂ := b21e231
                 grind)
              | exact superpose b21e231 b21e15
              | exact resolve b21e15 b21e231
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e231
            have b21e1677 : (k x y) = (k x (k x y)) := by
              first
              | (have i₁ := b21e1676
                 have i₂ := b21e15 (k x y)
                 grind)
              | exact superpose b21e15 b21e1676
              | exact resolve b21e1676 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1676
            have b21e2066 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b21e1677
                 have i₂ := b21e19 x y
                 grind)
              | exact superpose b21e19 b21e1677
              | (have j1 := b21e19 x y
                 grind)
              | exact resolve b21e1677 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1677
            have b21e2080 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x x) := by
              first
              | (have r₁ := b21e2066
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e2066 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2066
            have b21e2082 : x = y ∨ (M.op x y) = (k x (M.op x y)) := by
              first
              | (have i₁ := b21e2080
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e2080
              | exact resolve b21e2080 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2080
            have b21e2083 : (M.op x y) = (k x (M.op x y)) := by
              first
              | (have r₁ := b21e2082
                 have r₂ := b21e28
                 grind)
              | exact resolve b21e2082 b21e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e28 b21e2082
            have b21e2262 : (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
              first
              | (have i₁ := b21e19 x (M.op x y)
                 have i₂ := b21e2083
                 grind)
              | exact superpose b21e2083 b21e19
              | (have j0 := b21e19 x (M.op x y)
                 grind)
              | exact resolve b21e19 b21e2083
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2083
            have b21e2263 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
              first
              | (have i₁ := b21e2262
                 have i₂ := b21e41 x y
                 grind)
              | exact superpose b21e41 b21e2262
              | exact resolve b21e2262 b21e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e41 b21e2262
            have b21e2267 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
              first
              | (have i₁ := b21e2263
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e2263
              | exact resolve b21e2263 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2263
            have b21e2268 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
            clear b21e2267
            have b21e2273 : (M.op x y) = (M.op x (σ y)) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b21e2268
                 have i₂ := b21e34 x y
                 grind)
              | exact superpose b21e34 b21e2268
              | exact resolve b21e2268 b21e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e34 b21e2268
            have b21e2275 : x = (M.op x y) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b21e2273
                 have i₂ := b21e44
                 grind)
              | exact superpose b21e44 b21e2273
              | exact resolve b21e2273 b21e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e44 b21e2273
            have b21e2276 : x = (M.op x y) := by grind
            clear b21e2275
            have b21e2333 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e73 x x
                 have i₂ := b21e62
                 grind)
              | exact superpose b21e62 b21e73
              | exact resolve b21e73 b21e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e73
            have b21e2450 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by grind
            clear b21e2333
            have b21e2527 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e2450
                 have i₂ := b21e29
                 grind)
              | exact superpose b21e29 b21e2450
              | exact resolve b21e2450 b21e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e29 b21e2450
            have b21e2528 : (σ x) = (σ (k x y)) := by grind
            clear b21e2527
            have b21e2648 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b21e1399 X0
                 have i₂ := b21e2276
                 grind)
              | exact superpose b21e2276 b21e1399
              | exact resolve b21e1399 b21e2276
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1399
            have b21e2650 : (σ x) ≠ (M.op (σ x) x) := by
              first
              | (have i₁ := b21e147
                 have i₂ := b21e2276
                 grind)
              | exact superpose b21e2276 b21e147
              | exact resolve b21e147 b21e2276
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e147 b21e2276
            have b21e3118 : (σ (k x y)) = (M.op (σ x) x) := by
              first
              | (have i₁ := b21e62
                 have i₂ := b21e2648 (σ x)
                 grind)
              | exact superpose b21e2648 b21e62
              | exact resolve b21e62 b21e2648
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e62 b21e2648
            have b21e3166 : (σ x) = (M.op (σ x) x) := by
              first
              | (have i₁ := b21e3118
                 have i₂ := b21e2528
                 grind)
              | exact superpose b21e2528 b21e3118
              | exact resolve b21e3118 b21e2528
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2528 b21e3118
            have b21e3182 : False := by grind
            exact b21e3182
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b22e27 : x ≠ (M.op x x) := by grind
              have b22e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e30 : False := by grind
              exact b22e30
            · have b23e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b23e23 : y ≠ (M.op x x) := by grind
              have b23e24 : y ≠ (M.op y x) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b23e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              have b23e28 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
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
              have b23e37 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (σ y)) := by
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
              have b23e42 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X0 X2 X3 (M.op x x)
                   have i₂ := b23e15 X0 x x X1
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e44 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b23e15 X0 X1 X2 x
                   have i₂ := b23e15 X0 X3 X4 x
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e50 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b23e16 (k X0 (τ X1))
                   have i₂ := b23e31 X1 X0
                   grind)
                | exact superpose b23e31 b23e16
                | exact resolve b23e16 b23e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e31
              have b23e53 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
              have b23e56 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
              clear b23e53
              have b23e58 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e56
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e56 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e56
              have b23e59 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b23e58
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e58
                | exact resolve b23e58 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e58
              have b23e64 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ y)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e15 X0 X1 X2 x
                   have i₂ := b23e37 X0 x
                   grind)
                | exact superpose b23e37 b23e15
                | exact resolve b23e15 b23e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
              have b23e77 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e78 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (σ y)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b23e37 X1 X1
                   have i₂ := b23e20 X1 X0
                   grind)
                | (have i₁ := b23e37 X0 X1
                   have i₂ := b23e20 X0 (M.op X0 X1)
                   grind)
                | exact superpose b23e20 b23e37
                | (have j1 := b23e20 X1 X0
                   grind)
                | exact resolve b23e37 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e88 : (σ (k x y)) = (k (σ x) (σ (k x y))) := by grind
              have b23e89 : (M.op (σ x) (σ y)) = (M.op (σ (k x y)) (σ x)) := by
                first
                | (have i₁ := b23e37 (σ x) (σ x)
                   have i₂ := b23e59
                   grind)
                | exact superpose b23e59 b23e37
                | exact resolve b23e37 b23e59
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e92 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (σ (k x y))) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X0 (σ x) (σ x) X1
                   have i₂ := b23e59
                   grind)
                | exact superpose b23e59 b23e15
                | exact resolve b23e15 b23e59
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e93 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k x y))) := by
                intro X0
                first
                | (have i₁ := b23e92 X0 x
                   have i₂ := b23e37 X0 x
                   grind)
                | exact superpose b23e37 b23e92
                | exact resolve b23e92 b23e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e92
              have b23e95 : (σ (k x y)) = (σ (k x (k x y))) := by
                first
                | (have i₁ := b23e88
                   have i₂ := b23e21 x (k x y)
                   grind)
                | exact superpose b23e21 b23e88
                | exact resolve b23e88 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e88
              have b23e226 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = X4 ∨ (M.op (M.op X0 X1) X4) = (k (M.op X0 X1) X4) ∨ (M.op X4 (M.op X0 X1)) = X4 := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b23e20 (M.op X0 X1) X4
                   have i₂ := b23e44 (M.op X0 X1) X0 X1 X2 X3
                   grind)
                | (have i₁ := b23e20 (M.op X0 X1) X4
                   have i₂ := b23e44 (M.op X0 X1) X2 X3 X0 X1
                   grind)
                | exact superpose b23e44 b23e20
                | (have j0 := b23e20 (M.op X0 X1) X4
                   grind)
                | exact resolve b23e20 b23e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e44
              have b23e244 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) (σ y)) = X4 ∨ (M.op (M.op X0 X1) X4) = (k (M.op X0 X1) X4) ∨ (M.op X4 (M.op X0 X1)) = X4 := by
                intro X0 X1 X4
                first
                | (have i₁ := b23e226 X0 X1 x x X4
                   have i₂ := b23e64 (M.op X0 X1) x x
                   grind)
                | exact superpose b23e64 b23e226
                | (have j0 := b23e226 X0 X1 x x X4
                   grind)
                | exact resolve b23e226 b23e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e226
              have b23e269 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X4) = (k (M.op X0 X1) X4) ∨ (M.op (M.op X0 X1) (σ y)) = X4 ∨ (M.op X4 (σ y)) = X4 := by
                intro X0 X1 X4
                first
                | (have i₁ := b23e244 X0 X1 X4
                   have i₂ := b23e64 X4 X0 X1
                   grind)
                | exact superpose b23e64 b23e244
                | (have j0 := b23e244 X0 X1 X4
                   grind)
                | exact resolve b23e244 b23e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e244
              have b23e368 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X0 X3) X0) ∨ (M.op (M.op X0 X3) X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X0 X3) X0)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e19 X0 (M.op (M.op X0 X3) X0)
                   have i₂ := b23e42 X0 X3 X1 X2
                   grind)
                | exact superpose b23e42 b23e19
                | (have j0 := b23e19 X0 (M.op (M.op X0 X3) X0)
                   grind)
                | exact resolve b23e19 b23e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e42
              have b23e382 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X0 X3) X0)) := by
                intro X0 X3
                first
                | (have j0 := b23e368 X0 x x X3
                   grind)
                | (have r₁ := b23e368 X0 x x X3
                   have r₂ := b23e15 X0 x x X3
                   grind)
                | exact resolve b23e368 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e368
              have b23e413 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X0 X3) X0)) := by
                intro X0 X3
                first
                | (have i₁ := b23e382 X0 X3
                   have i₂ := b23e37 X0 X3
                   grind)
                | exact superpose b23e37 b23e382
                | (have j0 := b23e382 X0 X3
                   grind)
                | exact resolve b23e382 b23e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e382
              have b23e436 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (σ y))) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b23e413 X0 x
                   have i₂ := b23e37 X0 x
                   grind)
                | exact superpose b23e37 b23e413
                | (have j0 := b23e413 X0 x
                   grind)
                | exact resolve b23e413 b23e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e413
              have b23e933 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
                intro X0
                first
                | (have i₁ := b23e93 X0
                   have i₂ := b23e20 x y
                   grind)
                | exact superpose b23e20 b23e93
                | (have j1 := b23e20 x y
                   grind)
                | exact resolve b23e93 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e93
              have b23e975 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op y x) := by
                intro X0
                first
                | (have j0 := b23e933 X0
                   grind)
                | (have r₁ := b23e933 X0
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e933 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e933
              have b23e981 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
                intro X0
                first
                | (have j0 := b23e975 X0
                   grind)
                | (have r₁ := b23e975 X0
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e975 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e975
              have b23e1102 : (σ (M.op x y)) = (σ (k x (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b23e95
                   have i₂ := b23e20 x y
                   grind)
                | exact superpose b23e20 b23e95
                | (have j1 := b23e20 x y
                   grind)
                | exact resolve b23e95 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e1110 : (k x (k x y)) = (τ (σ (k x y))) := by
                first
                | (have i₁ := b23e16 (k x (k x y))
                   have i₂ := b23e95
                   grind)
                | exact superpose b23e95 b23e16
                | exact resolve b23e16 b23e95
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e95
              have b23e1111 : (k x y) = (k x (k x y)) := by
                first
                | (have i₁ := b23e1110
                   have i₂ := b23e16 (k x y)
                   grind)
                | exact superpose b23e16 b23e1110
                | exact resolve b23e1110 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1110
              have b23e1116 : (σ (M.op x y)) = (σ (k x (M.op x y))) ∨ y = (M.op y x) := by
                first
                | (have r₁ := b23e1102
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e1102 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1102
              have b23e1118 : (σ (M.op x y)) = (σ (k x (M.op x y))) := by
                first
                | (have r₁ := b23e1116
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e1116 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1116
              have b23e1242 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b23e1111
                   have i₂ := b23e20 x y
                   grind)
                | exact superpose b23e20 b23e1111
                | (have j1 := b23e20 x y
                   grind)
                | exact resolve b23e1111 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1111
              have b23e1248 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op y x) := by
                first
                | (have r₁ := b23e1242
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e1242 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1242
              have b23e1250 : (M.op x y) = (k x (M.op x y)) := by
                first
                | (have r₁ := b23e1248
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e1248 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1248
              have b23e1494 : (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
                first
                | (have i₁ := b23e20 x (M.op x y)
                   have i₂ := b23e1250
                   grind)
                | exact superpose b23e1250 b23e20
                | (have j0 := b23e20 x (M.op x y)
                   grind)
                | exact resolve b23e20 b23e1250
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e1495 : (M.op x y) = (M.op x (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
                first
                | (have i₁ := b23e1494
                   have i₂ := b23e64 x x y
                   grind)
                | exact superpose b23e64 b23e1494
                | exact resolve b23e1494 b23e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e64 b23e1494
              have b23e1497 : (M.op x y) = (M.op x (σ y)) ∨ (M.op x y) = (M.op x (σ y)) ∨ (M.op x y) = (M.op x x) := by
                first
                | (have i₁ := b23e1495
                   have i₂ := b23e37 x y
                   grind)
                | exact superpose b23e37 b23e1495
                | exact resolve b23e1495 b23e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1495
              have b23e1498 : (M.op x y) = (M.op x (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
              clear b23e1497
              have b23e1697 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b23e89
                   have i₂ := b23e20 x y
                   grind)
                | exact superpose b23e20 b23e89
                | (have j1 := b23e20 x y
                   grind)
                | exact resolve b23e89 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e89
              have b23e1722 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
                first
                | (have r₁ := b23e1697
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e1697 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1697
              have b23e1731 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) := by
                first
                | (have r₁ := b23e1722
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e1722 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1722
              have b23e2110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b23e75 x (M.op x y)
                   have i₂ := b23e1731
                   grind)
                | exact superpose b23e1731 b23e75
                | (have j0 := b23e75 x (M.op x y)
                   grind)
                | exact resolve b23e75 b23e1731
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e75 b23e1731
              have b23e2137 : (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
                first
                | (have r₁ := b23e2110
                   have r₂ := b23e22
                   grind)
                | exact resolve b23e2110 b23e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e2110
              have b23e2147 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b23e2137
                   have i₂ := b23e981 (σ x)
                   grind)
                | exact superpose b23e981 b23e2137
                | exact resolve b23e2137 b23e981
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e981 b23e2137
              have b23e2154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b23e2147
                   have i₂ := b23e1118
                   grind)
                | exact superpose b23e1118 b23e2147
                | exact resolve b23e2147 b23e1118
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1118 b23e2147
              have b23e2158 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
                first
                | (have r₁ := b23e2154
                   have r₂ := b23e22
                   grind)
                | exact resolve b23e2154 b23e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e2154
              have b23e2175 : (σ (M.op x y)) = (σ (k x y)) := by
                first
                | (have i₁ := b23e59
                   have i₂ := b23e2158
                   grind)
                | exact superpose b23e2158 b23e59
                | exact resolve b23e59 b23e2158
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e2158
              have b23e4635 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b23e78 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e78
              have b23e6806 : (M.op x x) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
                first
                | (have i₁ := b23e436 x
                   have i₂ := b23e1498
                   grind)
                | exact superpose b23e1498 b23e436
                | exact resolve b23e436 b23e1498
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e436 b23e1498
              have b23e6835 : (M.op x x) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by grind
              clear b23e6806
              have b23e6839 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
                first
                | (have i₁ := b23e6835
                   have i₂ := b23e1250
                   grind)
                | exact superpose b23e1250 b23e6835
                | exact resolve b23e6835 b23e1250
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1250 b23e6835
              have b23e6840 : (M.op x y) = (M.op x x) := by grind
              clear b23e6839
              have b23e8493 : ∀ X0 : G, (M.op (σ y) (σ y)) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e269 (σ y) (σ x) x
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e269
                | (have j0 := b23e269 X0 x X0
                   grind)
                | exact resolve b23e269 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e269
              have b23e8618 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have j0 := b23e8493 X0
                   have j1 := b23e4635 X0 (σ y)
                   grind)
                | (have r₁ := b23e8493 X0
                   have r₂ := b23e4635 X0 (σ y)
                   grind)
                | (have r₁ := b23e8493 (M.op x (σ y))
                   have r₂ := b23e4635 (M.op (σ y) (σ y)) x
                   grind)
                | (have r₁ := b23e8493 (σ y)
                   have r₂ := b23e4635 (k (σ y) (σ y)) (σ y)
                   grind)
                | exact resolve b23e8493 b23e4635
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e4635 b23e8493
              have b23e8646 : ∀ X0 : G, (τ (M.op (σ y) X0)) = (k y (τ X0)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e50 y X0
                   have i₂ := b23e8618 X0
                   grind)
                | exact superpose b23e8618 b23e50
                | (have j1 := b23e8618 X0
                   grind)
                | exact resolve b23e50 b23e8618
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e50 b23e8618
              have b23e13507 : (τ (σ y)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b23e8646 (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e8646
                | (have j0 := b23e8646 (σ x)
                   grind)
                | exact resolve b23e8646 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e8646
              have b23e13562 : (k y x) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b23e13507
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e13507
                | exact resolve b23e13507 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e13507
              have b23e13575 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
                first
                | (have i₁ := b23e13562
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e13562
                | exact resolve b23e13562 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e13562
              have b23e14401 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y x) := by
                first
                | (have i₁ := b23e22
                   have i₂ := b23e13575
                   grind)
                | exact superpose b23e13575 b23e22
                | exact resolve b23e22 b23e13575
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e14424 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by
                first
                | (have i₁ := b23e37 (σ x) (σ y)
                   have i₂ := b23e13575
                   grind)
                | exact superpose b23e13575 b23e37
                | exact resolve b23e37 b23e13575
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e37 b23e13575
              have b23e14464 : (σ x) = (σ (k x y)) ∨ y = (k y x) := by
                first
                | (have i₁ := b23e14424
                   have i₂ := b23e59
                   grind)
                | exact superpose b23e59 b23e14424
                | exact resolve b23e14424 b23e59
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e59 b23e14424
              have b23e14475 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k y x) := by
                first
                | (have i₁ := b23e14401
                   have i₂ := b23e6840
                   grind)
                | exact superpose b23e6840 b23e14401
                | exact resolve b23e14401 b23e6840
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e14401
              have b23e14480 : (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by
                first
                | (have i₁ := b23e14464
                   have i₂ := b23e2175
                   grind)
                | exact superpose b23e2175 b23e14464
                | exact resolve b23e14464 b23e2175
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e2175 b23e14464
              have b23e14488 : (σ x) = (σ (M.op x x)) ∨ y = (k y x) := by
                first
                | (have i₁ := b23e14480
                   have i₂ := b23e6840
                   grind)
                | exact superpose b23e6840 b23e14480
                | exact resolve b23e14480 b23e6840
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e14480
              have b23e14490 : y = (k y x) := by
                first
                | (have r₁ := b23e14488
                   have r₂ := b23e14475
                   grind)
                | exact resolve b23e14488 b23e14475
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e14475 b23e14488
              have b23e14884 : y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b23e20 y x
                   have i₂ := b23e14490
                   grind)
                | exact superpose b23e14490 b23e20
                | (have j0 := b23e20 y x
                   grind)
                | exact resolve b23e20 b23e14490
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e14887 : y = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
                first
                | (have i₁ := b23e77 x y
                   have i₂ := b23e14490
                   grind)
                | exact superpose b23e14490 b23e77
                | (have j0 := b23e77 y x
                   grind)
                | exact resolve b23e77 b23e14490
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e77 b23e14490
              have b23e14888 : x = y ∨ x = (M.op x y) := by
                first
                | (have r₁ := b23e14887
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e14887 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e14887
              have b23e14891 : x = (M.op y y) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b23e14884
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e14884 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e14884
              have b23e14896 : x = (M.op x x) ∨ x = y := by
                first
                | (have i₁ := b23e14888
                   have i₂ := b23e6840
                   grind)
                | exact superpose b23e6840 b23e14888
                | exact resolve b23e14888 b23e6840
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e14888
              have b23e14899 : x = (M.op x x) ∨ x = (M.op y y) := by
                first
                | (have i₁ := b23e14891
                   have i₂ := b23e6840
                   grind)
                | exact superpose b23e6840 b23e14891
                | exact resolve b23e14891 b23e6840
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e6840 b23e14891
              have b23e14904 : x = y := by
                first
                | (have r₁ := b23e14896
                   have r₂ := b23e28
                   grind)
                | exact resolve b23e14896 b23e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e14896
              have b23e14907 : x = (M.op y y) := by
                first
                | (have r₁ := b23e14899
                   have r₂ := b23e28
                   grind)
                | exact resolve b23e14899 b23e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e14899
              have b23e14914 : x = (M.op x x) := by
                first
                | (have i₁ := b23e14907
                   have i₂ := b23e14904
                   grind)
                | exact superpose b23e14904 b23e14907
                | exact resolve b23e14907 b23e14904
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e14904 b23e14907
              have b23e14920 : False := by grind
              exact b23e14920
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : y ≠ (M.op x x) := by grind
            have b24e23 : y ≠ (M.op y x) := by grind
            have b24e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b24e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b24e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e28 : x ≠ y := by
              first
              | (have i₁ := b24e22
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e22
              | exact resolve b24e22 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e82 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b24e24
                 have i₂ := b24e19 (σ x) X0
                 grind)
              | (have i₁ := b24e24
                 have i₂ := b24e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b24e19 b24e24
              | (have j1 := b24e19 (σ x) X0
                 grind)
              | (have r₁ := b24e24
                 have r₂ := b24e19 (σ x) (σ y)
                 grind)
              | exact resolve b24e24 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1261 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b24e82 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e82
            have b24e1262 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b24e1261
                 have r₂ := b24e25
                 grind)
              | exact resolve b24e1261 b24e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1261
            have b24e1263 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b24e1262
                 have i₂ := b24e20 x y
                 grind)
              | exact superpose b24e20 b24e1262
              | exact resolve b24e1262 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1262
            have b24e1264 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e1263
                 grind)
              | exact superpose b24e1263 b24e21
              | exact resolve b24e21 b24e1263
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1263
            have b24e1439 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b24e1264
                 have i₂ := b24e19 x y
                 grind)
              | exact superpose b24e19 b24e1264
              | (have j1 := b24e19 x y
                 grind)
              | exact resolve b24e1264 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1264
            have b24e1440 : y = (M.op x x) ∨ y = (M.op y x) := by grind
            clear b24e1439
            have b24e1443 : y = (M.op x x) := by
              first
              | (have r₁ := b24e1440
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e1440 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1440
            have b24e1446 : x = y := by
              first
              | (have i₁ := b24e1443
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e1443
              | exact resolve b24e1443 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1443
            have b24e1447 : False := by grind
            exact b24e1447
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b25e27 : x ≠ (M.op x x) := by grind
              have b25e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e30 : False := by grind
              exact b25e30
            · have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : y ≠ (M.op x x) := by grind
              have b26e24 : y ≠ (M.op y x) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b26e26 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e71 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e20 (σ x) X0
                   grind)
                | (have i₁ := b26e25
                   have i₂ := b26e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b26e20 b26e25
                | (have j1 := b26e20 (σ x) X0
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 (σ x) (σ y)
                   grind)
                | exact resolve b26e25 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e412 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b26e71 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e71
              have b26e413 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b26e412
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e412 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e412
              have b26e414 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e413
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e413
                | exact resolve b26e413 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e413
              have b26e415 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e414
                   grind)
                | exact superpose b26e414 b26e22
                | exact resolve b26e22 b26e414
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e414
              have b26e610 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b26e415
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e415
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e415 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e415
              have b26e611 : y = (M.op x x) ∨ y = (M.op y x) := by grind
              clear b26e610
              have b26e613 : y = (M.op y x) := by
                first
                | (have r₁ := b26e611
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e611 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e611
              have b26e615 : False := by grind
              exact b26e615
