import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e40 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e41 : (M.op x y) = (k x y) := by grind
      have b0e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e40
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e40
        | exact resolve b0e40 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e44 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e43
        | exact resolve b0e43 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e43
      have b0e45 : False := by grind
      exact b0e45
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b1e39 : (M.op x y) = (k x y) := by grind
        have b1e68 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b1e81 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e68
             have r₂ := b1e21
             grind)
          | exact resolve b1e68 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e82 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e81
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e81
          | exact resolve b1e81 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81
        have b1e83 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e82
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e82
          | exact resolve b1e82 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e82
        have b1e84 : False := by grind
        exact b1e84
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e49 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e71 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e68 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e469 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0
             have i₂ := b2e49 X0 X1
             grind)
          | (have i₁ := b2e71 X0
             have i₂ := b2e49 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e49 b2e71
          | (have j1 := b2e49 X1 X0
             grind)
          | exact resolve b2e71 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e71
        have b2e503 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e469 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e469
        have b2e4564 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e503 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e503
        have b2e4565 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e4564 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4564
        have b2e4587 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e4565 (σ X0)
             grind)
          | exact superpose b2e4565 b2e18
          | exact resolve b2e18 b2e4565
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4594 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e4587 X0
             have i₂ := b2e4565 X0
             grind)
          | exact superpose b2e4565 b2e4587
          | exact resolve b2e4587 b2e4565
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4565 b2e4587
        have b2e4981 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e4594 x
             grind)
          | exact superpose b2e4594 b2e21
          | exact resolve b2e21 b2e4594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4594
        have b2e5041 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e4981
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4981
          | exact resolve b2e4981 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4981
        have b2e5042 : False := by grind
        exact b2e5042
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e38 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e38
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e38
          | exact resolve b3e38 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e67 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        have b3e79 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e67
             have r₂ := b3e20
             grind)
          | exact resolve b3e67 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e112 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e19
          | exact resolve b3e19 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e117 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e112
             have i₂ := b3e79
             grind)
          | exact superpose b3e79 b3e112
          | exact resolve b3e112 b3e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79 b3e112
        have b3e118 : False := by grind
        exact b3e118
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
          have b4e77 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          have b4e78 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          have b4e90 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e78
               have r₂ := b4e21
               grind)
            | exact resolve b4e78 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e91 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e77
               have r₂ := b4e23
               grind)
            | exact resolve b4e77 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e92 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e91
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e91
            | exact resolve b4e91 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91
          have b4e93 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e92
               have i₂ := b4e90
               grind)
            | exact superpose b4e90 b4e92
            | exact resolve b4e92 b4e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90 b4e92
          have b4e94 : False := by grind
          exact b4e94
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e76 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e79 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e76 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e467 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e79 X0
               have i₂ := b5e56 X0 X1
               grind)
            | (have i₁ := b5e79 X0
               have i₂ := b5e56 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e56 b5e79
            | (have j1 := b5e56 X1 X0
               grind)
            | exact resolve b5e79 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56 b5e79
          have b5e499 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e467 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e467
          have b5e4549 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e499 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e499
          have b5e4550 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e4549 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4549
          have b5e4572 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e4550 (σ X0)
               grind)
            | exact superpose b5e4550 b5e19
            | exact resolve b5e19 b5e4550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4579 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e4572 X0
               have i₂ := b5e4550 X0
               grind)
            | exact superpose b5e4550 b5e4572
            | exact resolve b5e4572 b5e4550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4550 b5e4572
          have b5e4969 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e4579 y
               grind)
            | exact superpose b5e4579 b5e24
            | exact resolve b5e24 b5e4579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4579
          have b5e5028 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e4969
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e4969
            | exact resolve b5e4969 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4969
          have b5e5029 : False := by grind
          exact b5e5029
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b6e36 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b6e38 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e36
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e36
          | exact resolve b6e36 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b6e67 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e38
             grind)
          | exact superpose b6e38 b6e19
          | exact resolve b6e19 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e71 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e80 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e81 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e80 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e83 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e71 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e85 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e67
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e67
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e67 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e86 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e85
             have r₂ := b6e20
             grind)
          | exact resolve b6e85 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85
        have b6e87 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
          first
          | (have r₁ := b6e86
             have r₂ := b6e21
             grind)
          | exact resolve b6e86 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e1715 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e64 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e64
          | exact resolve b6e64 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e1974 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1715
        have b6e2037 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1974
             grind)
          | exact superpose b6e1974 b6e13
          | exact resolve b6e13 b6e1974
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1974
        have b6e2051 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2037
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2037
          | exact resolve b6e2037 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2037
        have b6e2319 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e83 x x
             have i₂ := b6e2051
             grind)
          | exact superpose b6e2051 b6e83
          | (have j0 := b6e83 x y
             grind)
          | exact resolve b6e83 b6e2051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e2320 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e2319
        have b6e2330 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e2320
             have r₂ := b6e20
             grind)
          | exact resolve b6e2320 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2320
        have b6e2607 : (M.op x x) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e81 x
             have i₂ := b6e2330
             grind)
          | exact superpose b6e2330 b6e81
          | exact resolve b6e81 b6e2330
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81 b6e2330
        have b6e3320 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2051
             have i₂ := b6e2607
             grind)
          | exact superpose b6e2607 b6e2051
          | exact resolve b6e2051 b6e2607
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2051 b6e2607
        have b6e3323 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3320
        have b6e3325 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3323
             have r₂ := b6e20
             grind)
          | exact resolve b6e3323 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3323
        have b6e3880 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e3325
             grind)
          | exact superpose b6e3325 b6e13
          | exact resolve b6e13 b6e3325
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3325
        have b6e3897 : x = y := by
          first
          | (have i₁ := b6e3880
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3880
          | exact resolve b6e3880 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3880
        have b6e4042 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e87
             have i₂ := b6e3897
             grind)
          | exact superpose b6e3897 b6e87
          | exact resolve b6e87 b6e3897
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87 b6e3897
        have b6e4054 : False := by grind
        exact b6e4054
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b7e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b7e82 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          have b7e83 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e92 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e93 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e92 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e95 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e83 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e96 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e82
               have r₂ := b7e23
               grind)
            | exact resolve b7e82 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e97 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e96
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e96
            | exact resolve b7e96 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e98 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e97
               grind)
            | exact superpose b7e97 b7e20
            | exact resolve b7e20 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97
          have b7e117 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e98
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e98
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e98 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e118 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e117
               have r₂ := b7e21
               grind)
            | exact resolve b7e117 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e117
          have b7e119 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b7e118
               have r₂ := b7e22
               grind)
            | exact resolve b7e118 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118
          have b7e1784 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e70 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e70
            | exact resolve b7e70 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e2045 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e1784
          have b7e2109 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e2045
               grind)
            | exact superpose b7e2045 b7e14
            | exact resolve b7e14 b7e2045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2045
          have b7e2123 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2109
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2109
            | exact resolve b7e2109 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2109
          have b7e2397 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e95 y y
               have i₂ := b7e2123
               grind)
            | exact superpose b7e2123 b7e95
            | (have j0 := b7e95 y x
               grind)
            | exact resolve b7e95 b7e2123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e2398 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2397
          have b7e2408 : y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e2398
               have r₂ := b7e22
               grind)
            | exact resolve b7e2398 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2398
          have b7e2691 : (M.op y y) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e93 y
               have i₂ := b7e2408
               grind)
            | exact superpose b7e2408 b7e93
            | exact resolve b7e93 b7e2408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93 b7e2408
          have b7e3422 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2123
               have i₂ := b7e2691
               grind)
            | exact superpose b7e2691 b7e2123
            | exact resolve b7e2123 b7e2691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2123 b7e2691
          have b7e3425 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3422
          have b7e3427 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e3425
               have r₂ := b7e22
               grind)
            | exact resolve b7e3425 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3425
          have b7e4018 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e3427
               grind)
            | exact superpose b7e3427 b7e14
            | exact resolve b7e14 b7e3427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3427
          have b7e4031 : x = y := by
            first
            | (have i₁ := b7e4018
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e4018
            | exact resolve b7e4018 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4018
          have b7e4192 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e119
               have i₂ := b7e4031
               grind)
            | exact superpose b7e4031 b7e119
            | exact resolve b7e119 b7e4031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e119 b7e4031
          have b7e4200 : False := by grind
          exact b7e4200
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e63 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
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
          have b8e373 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e63 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e374 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e373
               have r₂ := b8e23
               grind)
            | exact resolve b8e373 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e373
          have b8e375 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e374
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e374
            | exact resolve b8e374 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e374
          have b8e376 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e375
               grind)
            | exact superpose b8e375 b8e20
            | exact resolve b8e20 b8e375
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e375
          have b8e469 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e376
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e376
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e376 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e376
          have b8e475 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e469
          have b8e478 : y = (M.op x x) := by
            first
            | (have r₁ := b8e475
               have r₂ := b8e22
               grind)
            | exact resolve b8e475 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e475
          have b8e479 : False := by grind
          exact b8e479

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        grind
      have b0e81 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e78 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e129 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e81 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e81
        | exact resolve b0e81 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e130 : (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e81 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e81
        | exact resolve b0e81 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81
      have b0e133 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e129
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e129
        | exact resolve b0e129 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129
      have b0e134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e133
           have i₂ := b0e130
           grind)
        | exact superpose b0e130 b0e133
        | exact resolve b0e133 b0e130
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130 b0e133
      have b0e135 : False := by grind
      exact b0e135
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e38 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e40 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e38
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e38
          | exact resolve b1e38 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e75 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e75 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e112 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e19
          | exact resolve b1e19 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e161 : (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e78 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e78
          | exact resolve b1e78 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78
        have b1e167 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e112
             have i₂ := b1e161
             grind)
          | exact superpose b1e161 b1e112
          | exact resolve b1e112 b1e161
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e112 b1e161
        have b1e169 : False := by grind
        exact b1e169
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e68 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e71 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e68 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e472 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0
             have i₂ := b2e49 X0 X1
             grind)
          | (have i₁ := b2e71 X0
             have i₂ := b2e49 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e49 b2e71
          | (have j1 := b2e49 X1 X0
             grind)
          | exact resolve b2e71 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e71
        have b2e506 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e472 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e472
        have b2e4569 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e506 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e506
        have b2e4570 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e4569 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4569
        have b2e4593 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e4570 (σ X0)
             grind)
          | exact superpose b2e4570 b2e18
          | exact resolve b2e18 b2e4570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4600 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e4593 X0
             have i₂ := b2e4570 X0
             grind)
          | exact superpose b2e4570 b2e4593
          | exact resolve b2e4593 b2e4570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4570 b2e4593
        have b2e4987 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e4600 x
             grind)
          | exact superpose b2e4600 b2e21
          | exact resolve b2e21 b2e4600
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4600
        have b2e5047 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e4987
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4987
          | exact resolve b2e4987 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4987
        have b2e5048 : False := by grind
        exact b2e5048
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e39 : (M.op x y) = (k y x) := by grind
        have b3e66 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b3e80 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e66
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e66
          | exact resolve b3e66 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e81 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e39
             grind)
          | exact superpose b3e39 b3e80
          | exact resolve b3e80 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e82 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b3e81
             have r₂ := b3e19
             grind)
          | exact resolve b3e81 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e90 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e82
        have b3e93 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e90
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e90
          | exact resolve b3e90 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90
        have b3e94 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e93
             have i₂ := b3e39
             grind)
          | exact superpose b3e39 b3e93
          | exact resolve b3e93 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e93
        have b3e95 : False := by grind
        exact b3e95
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e44 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e45 : (M.op x y) = (k y x) := by grind
          have b4e47 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e44
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e44
            | exact resolve b4e44 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e48 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e47
               have i₂ := b4e45
               grind)
            | exact superpose b4e45 b4e47
            | exact resolve b4e47 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e47
          have b4e49 : False := by grind
          exact b4e49
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e76 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e76 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e468 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e79 X0
               have i₂ := b5e56 X0 X1
               grind)
            | (have i₁ := b5e79 X0
               have i₂ := b5e56 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e56 b5e79
            | (have j1 := b5e56 X1 X0
               grind)
            | exact resolve b5e79 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56 b5e79
          have b5e500 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e468 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e468
          have b5e4544 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e500 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e500
          have b5e4545 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e4544 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4544
          have b5e4566 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e4545 (σ X0)
               grind)
            | exact superpose b5e4545 b5e19
            | exact resolve b5e19 b5e4545
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4573 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e4566 X0
               have i₂ := b5e4545 X0
               grind)
            | exact superpose b5e4545 b5e4566
            | exact resolve b5e4566 b5e4545
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4545 b5e4566
          have b5e4963 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e4573 y
               grind)
            | exact superpose b5e4573 b5e24
            | exact resolve b5e24 b5e4573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4573
          have b5e5022 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e4963
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e4963
            | exact resolve b5e4963 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4963
          have b5e5023 : False := by grind
          exact b5e5023
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e36 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b6e38 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e36
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e36
          | exact resolve b6e36 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e62 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e70 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e79 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e82 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e70 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e115 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e80 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e80
          | exact resolve b6e80 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e121 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e115
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e115
          | exact resolve b6e115 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e115
        have b6e122 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e121
             grind)
          | exact superpose b6e121 b6e19
          | exact resolve b6e19 b6e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e121
        have b6e511 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e122
             have i₂ := b6e62 x y
             grind)
          | exact superpose b6e62 b6e122
          | (have j1 := b6e62 x y
             grind)
          | exact resolve b6e122 b6e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62 b6e122
        have b6e557 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        clear b6e511
        have b6e567 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e557
             have r₂ := b6e20
             grind)
          | exact resolve b6e557 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e557
        have b6e1711 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e64 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e64
          | exact resolve b6e64 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e1963 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1711
        have b6e2038 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1963
             grind)
          | exact superpose b6e1963 b6e13
          | exact resolve b6e13 b6e1963
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1963
        have b6e2052 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2038
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2038
          | exact resolve b6e2038 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2038
        have b6e2316 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e82 x x
             have i₂ := b6e2052
             grind)
          | exact superpose b6e2052 b6e82
          | (have j0 := b6e82 x y
             grind)
          | exact resolve b6e82 b6e2052
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e2317 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e2316
        have b6e2327 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e2317
             have r₂ := b6e20
             grind)
          | exact resolve b6e2317 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2317
        have b6e2606 : (M.op x x) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e80 x
             have i₂ := b6e2327
             grind)
          | exact superpose b6e2327 b6e80
          | exact resolve b6e80 b6e2327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80 b6e2327
        have b6e3332 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2052
             have i₂ := b6e2606
             grind)
          | exact superpose b6e2606 b6e2052
          | exact resolve b6e2052 b6e2606
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2052 b6e2606
        have b6e3335 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3332
        have b6e3337 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3335
             have r₂ := b6e20
             grind)
          | exact resolve b6e3335 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3335
        have b6e3855 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e3337
             grind)
          | exact superpose b6e3337 b6e19
          | exact resolve b6e19 b6e3337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3858 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e38
             have i₂ := b6e3337
             grind)
          | exact superpose b6e3337 b6e38
          | exact resolve b6e38 b6e3337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e3869 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e3337
             grind)
          | exact superpose b6e3337 b6e13
          | exact resolve b6e13 b6e3337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3886 : x = y := by
          first
          | (have i₁ := b6e3869
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3869
          | exact resolve b6e3869 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3869
        have b6e3892 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e3858
             have i₂ := b6e567
             grind)
          | exact superpose b6e567 b6e3858
          | exact resolve b6e3858 b6e567
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e567 b6e3858
        have b6e3893 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e3855
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e3855
          | exact resolve b6e3855 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3855
        have b6e3902 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b6e3892
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e3892
          | exact resolve b6e3892 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3892
        have b6e3903 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e3893
             have i₂ := b6e3337
             grind)
          | exact superpose b6e3337 b6e3893
          | exact resolve b6e3893 b6e3337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3893
        have b6e3909 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b6e3902
             have i₂ := b6e3337
             grind)
          | exact superpose b6e3337 b6e3902
          | exact resolve b6e3902 b6e3337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3337 b6e3902
        have b6e3910 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e3903
             have i₂ := b6e3886
             grind)
          | exact superpose b6e3886 b6e3903
          | exact resolve b6e3903 b6e3886
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3903
        have b6e3911 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e3909
             have i₂ := b6e3886
             grind)
          | exact superpose b6e3886 b6e3909
          | exact resolve b6e3909 b6e3886
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3886 b6e3909
        have b6e3912 : False := by grind
        exact b6e3912
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e46 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b7e48 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e46
            | exact resolve b7e46 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e49 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e20
            | exact resolve b7e20 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b7e74 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e49
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e49 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e75 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e22
               grind)
            | exact resolve b7e74 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e76 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e21
               grind)
            | exact resolve b7e75 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e78 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e87 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e88 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e87 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e90 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e1933 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e71 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e71
            | exact resolve b7e71 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e2200 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e1933
          have b7e2294 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e2200
               grind)
            | exact superpose b7e2200 b7e14
            | exact resolve b7e14 b7e2200
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2200
          have b7e2308 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2294
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2294
            | exact resolve b7e2294 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2294
          have b7e2602 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e90 y y
               have i₂ := b7e2308
               grind)
            | exact superpose b7e2308 b7e90
            | (have j0 := b7e90 y x
               grind)
            | exact resolve b7e90 b7e2308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e2603 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2602
          have b7e2613 : y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e2603
               have r₂ := b7e22
               grind)
            | exact resolve b7e2603 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2603
          have b7e2922 : (M.op y y) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e88 y
               have i₂ := b7e2613
               grind)
            | exact superpose b7e2613 b7e88
            | exact resolve b7e88 b7e2613
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88 b7e2613
          have b7e3711 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2308
               have i₂ := b7e2922
               grind)
            | exact superpose b7e2922 b7e2308
            | exact resolve b7e2308 b7e2922
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2308 b7e2922
          have b7e3714 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3711
          have b7e3716 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e3714
               have r₂ := b7e22
               grind)
            | exact resolve b7e3714 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3714
          have b7e4344 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e3716
               grind)
            | exact superpose b7e3716 b7e14
            | exact resolve b7e14 b7e3716
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3716
          have b7e4357 : x = y := by
            first
            | (have i₁ := b7e4344
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e4344
            | exact resolve b7e4344 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4344
          have b7e4517 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e76
               have i₂ := b7e4357
               grind)
            | exact superpose b7e4357 b7e76
            | exact resolve b7e76 b7e4357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76 b7e4357
          have b7e4532 : False := by grind
          exact b7e4532
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e62 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e358 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e62 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e359 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e358
               have r₂ := b8e24
               grind)
            | exact resolve b8e358 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e358
          have b8e360 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e359
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e359
            | exact resolve b8e359 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e359
          have b8e361 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e360
               grind)
            | exact superpose b8e360 b8e20
            | exact resolve b8e20 b8e360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e360
          have b8e379 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e361
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e361
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e361 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e361
          have b8e380 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e379
          have b8e381 : x = (M.op y y) := by
            first
            | (have r₁ := b8e380
               have r₂ := b8e21
               grind)
            | exact resolve b8e380 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e380
          have b8e383 : False := by grind
          exact b8e383

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
           have i₂ := b0e26 X0 X1
           grind)
        | exact superpose b0e26 b0e12
        | exact resolve b0e12 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e53 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e27 X0 X1
           have i₂ := b0e16 X1 (τ X0)
           grind)
        | exact superpose b0e16 b0e27
        | (have j1 := b0e16 X1 (τ X0)
           grind)
        | exact resolve b0e27 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e16 (σ X1) (σ X0)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
      have b0e191 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e54 x y
           grind)
        | exact superpose b0e54 b0e18
        | (have j1 := b0e54 x y
           grind)
        | exact resolve b0e18 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e203 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e54 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e204 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e54 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e497 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e53 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e53
        | exact resolve b0e53 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e531 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e497 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e497
        | (have j0 := b0e497 X0 X1
           grind)
        | exact resolve b0e497 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e497
      have b0e700 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e203 (τ X1) (τ X0)
           have i₂ := b0e59 X1 X0
           grind)
        | exact superpose b0e59 b0e203
        | (have j0 := b0e203 (τ X1) (τ X0)
           grind)
        | exact resolve b0e203 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e710 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e700 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e700
        | (have j0 := b0e700 X0 X1
           grind)
        | exact resolve b0e700 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e700
      have b0e713 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e710 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e710
        | (have j0 := b0e710 X0 X1
           grind)
        | exact resolve b0e710 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e710
      have b0e715 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e713 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e713
        | (have j0 := b0e713 X0 X1
           grind)
        | exact resolve b0e713 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e713
      have b0e716 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e715 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e715
        | (have j0 := b0e715 X0 X1
           grind)
        | exact resolve b0e715 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e715
      have b0e717 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e716 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e716
        | (have j0 := b0e716 X0 X1
           grind)
        | exact resolve b0e716 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e716
      have b0e718 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e717 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e717
        | (have j0 := b0e717 X0 X1
           grind)
        | exact resolve b0e717 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e717
      have b0e733 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e204 (τ X1) (τ X0)
           have i₂ := b0e59 X1 X0
           grind)
        | exact superpose b0e59 b0e204
        | (have j0 := b0e204 (τ X1) (τ X0)
           grind)
        | exact resolve b0e204 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e742 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e733 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e733
        | (have j0 := b0e733 X0 X1
           grind)
        | exact resolve b0e733 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e733
      have b0e745 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e742 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e742
        | (have j0 := b0e742 X0 X1
           grind)
        | exact resolve b0e742 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e742
      have b0e747 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e745 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e745
        | (have j0 := b0e745 X0 X1
           grind)
        | exact resolve b0e745 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e745
      have b0e748 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e747 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e747
        | (have j0 := b0e747 X0 X1
           grind)
        | exact resolve b0e747 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e747
      have b0e749 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e748 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e748
        | (have j0 := b0e748 X0 X1
           grind)
        | exact resolve b0e748 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e748
      have b0e750 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e749 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e749
        | (have j0 := b0e749 X0 X1
           grind)
        | exact resolve b0e749 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e749
      have b0e761 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e191
           have i₂ := b0e531 x y
           grind)
        | exact superpose b0e531 b0e191
        | (have j1 := b0e531 (σ x) (σ y)
           grind)
        | (have r₁ := b0e191
           have r₂ := b0e531 x y
           grind)
        | exact resolve b0e191 b0e531
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e191 b0e531
      have b0e762 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e761
      have b0e40814 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e762
           grind)
        | exact superpose b0e762 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e762
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e762
           grind)
        | exact resolve b0e14 b0e762
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e762
      have b0e40826 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e40814
      have b0e40827 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e40826
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e40826
        | exact resolve b0e40826 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40826
      have b0e41951 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e40827
           grind)
        | exact superpose b0e40827 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e40827
           grind)
        | exact resolve b0e14 b0e40827
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41952 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e40827
           grind)
        | exact superpose b0e40827 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e40827
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e40827
           grind)
        | exact resolve b0e15 b0e40827
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40827
      have b0e41966 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e41952
      have b0e41969 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e41966
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e41966
        | exact resolve b0e41966 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41966
      have b0e41970 : (σ y) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e41951
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e41951
        | exact resolve b0e41951 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41951
      have b0e41971 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e41970
      have b0e218383 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e41969
           grind)
        | exact superpose b0e41969 b0e12
        | exact resolve b0e12 b0e41969
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41969
      have b0e218714 : (k y x) = (τ (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e218383
           have r₂ := b0e41971
           grind)
        | exact resolve b0e218383 b0e41971
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41971 b0e218383
      have b0e218791 : x = (k y x) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e218714
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e218714
        | exact resolve b0e218714 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e218714
      have b0e218792 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have j1 := b0e750 y x
           grind)
        | (have r₁ := b0e218791
           have r₂ := b0e750 y x
           grind)
        | exact resolve b0e218791 b0e750
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e750 b0e218791
      have b0e220471 : (k y x) = (τ (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e218792
           grind)
        | exact superpose b0e218792 b0e12
        | exact resolve b0e12 b0e218792
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e218792
      have b0e220704 : y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e220471
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e220471
        | exact resolve b0e220471 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e220471
      have b0e220705 : x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have j1 := b0e718 y x
           grind)
        | (have r₁ := b0e220704
           have r₂ := b0e718 y x
           grind)
        | exact resolve b0e220704 b0e718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e718 b0e220704
      have b0e222418 : x ≠ x ∨ y = (k y x) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e220705
           grind)
        | exact superpose b0e220705 b0e14
        | (have j0 := b0e14 y x
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e220705
           grind)
        | exact resolve b0e14 b0e220705
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e222433 : x ≠ y ∨ y = (M.op x y) := by grind
      have b0e222434 : y = (k y x) ∨ y = (M.op x y) := by grind
      clear b0e222418
      have b0e225768 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e203 x y
           have i₂ := b0e222434
           grind)
        | exact superpose b0e222434 b0e203
        | (have j0 := b0e203 x y
           grind)
        | exact resolve b0e203 b0e222434
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e203
      have b0e226007 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
      clear b0e225768
      have b0e252100 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e226007
           grind)
        | exact superpose b0e226007 b0e18
        | exact resolve b0e18 b0e226007
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e226007
      have b0e255633 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e252100
           have i₂ := b0e220705
           grind)
        | exact superpose b0e220705 b0e252100
        | exact resolve b0e252100 b0e220705
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e252100
      have b0e255636 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
      clear b0e255633
      have b0e255637 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e255636
           have r₂ := b0e222433
           grind)
        | exact resolve b0e255636 b0e222433
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e255636
      have b0e257428 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e255637
           grind)
        | exact superpose b0e255637 b0e18
        | exact resolve b0e18 b0e255637
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e257432 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e255637
           grind)
        | exact superpose b0e255637 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e255637
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e255637
           grind)
        | exact resolve b0e15 b0e255637
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e255637
      have b0e257450 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
      clear b0e257432
      have b0e257453 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e257450
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e257450
        | exact resolve b0e257450 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e257450
      have b0e259261 : (σ x) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e257428
           have i₂ := b0e220705
           grind)
        | exact superpose b0e220705 b0e257428
        | exact resolve b0e257428 b0e220705
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e220705 b0e257428
      have b0e259265 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e259261
           have r₂ := b0e222433
           grind)
        | exact resolve b0e259261 b0e222433
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e222433 b0e259261
      have b0e264392 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e257453
           have i₂ := b0e222434
           grind)
        | exact superpose b0e222434 b0e257453
        | exact resolve b0e257453 b0e222434
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e222434 b0e257453
      have b0e264600 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
      clear b0e264392
      have b0e264756 : y = (M.op x y) := by
        first
        | (have r₁ := b0e264600
           have r₂ := b0e259265
           grind)
        | exact resolve b0e264600 b0e259265
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e259265 b0e264600
      have b0e266446 : x ≠ y ∨ y = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e264756
           grind)
        | exact superpose b0e264756 b0e14
        | (have j0 := b0e14 y x
           grind)
        | exact resolve b0e14 b0e264756
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e266447 : y ≠ y ∨ x = y ∨ x = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e264756
           grind)
        | exact superpose b0e264756 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e264756
           grind)
        | exact resolve b0e15 b0e264756
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e266465 : x = (k y x) ∨ x = y := by grind
      clear b0e266447
      have b0e269951 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e204 x y
           have i₂ := b0e266465
           grind)
        | exact superpose b0e266465 b0e204
        | (have j0 := b0e204 x y
           grind)
        | exact resolve b0e204 b0e266465
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e204
      have b0e270075 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
      clear b0e269951
      have b0e292976 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e270075
           grind)
        | exact superpose b0e270075 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e270075
           grind)
        | exact resolve b0e14 b0e270075
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e270075
      have b0e292992 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
      clear b0e292976
      have b0e292993 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e292992
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e292992
        | exact resolve b0e292992 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e292992
      have b0e296637 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e292993
           grind)
        | exact superpose b0e292993 b0e18
        | exact resolve b0e18 b0e292993
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e292993
      have b0e296665 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e296637
           have i₂ := b0e264756
           grind)
        | exact superpose b0e264756 b0e296637
        | exact resolve b0e296637 b0e264756
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e296637
      have b0e296666 : (σ y) = (σ (k y x)) ∨ x = y := by grind
      clear b0e296665
      have b0e298497 : (k y x) = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e296666
           grind)
        | exact superpose b0e296666 b0e12
        | exact resolve b0e12 b0e296666
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e296666
      have b0e298714 : y = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e298497
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e298497
        | exact resolve b0e298497 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e298497
      have b0e298715 : y = (k y x) := by
        first
        | (have r₁ := b0e298714
           have r₂ := b0e266446
           grind)
        | exact resolve b0e298714 b0e266446
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e266446 b0e298714
      have b0e300579 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e266465
           have i₂ := b0e298715
           grind)
        | exact superpose b0e298715 b0e266465
        | exact resolve b0e266465 b0e298715
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e266465 b0e298715
      have b0e300709 : x = y := by grind
      clear b0e300579
      have b0e302086 : (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e300709
           grind)
        | exact superpose b0e300709 b0e18
        | exact resolve b0e18 b0e300709
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e302088 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e300709
           grind)
        | exact superpose b0e300709 b0e20
        | exact resolve b0e20 b0e300709
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e302184 : y = (M.op y y) := by
        first
        | (have i₁ := b0e264756
           have i₂ := b0e300709
           grind)
        | exact superpose b0e300709 b0e264756
        | exact resolve b0e264756 b0e300709
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e264756 b0e300709
      have b0e302229 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e302086
           have i₂ := b0e302088
           grind)
        | exact superpose b0e302088 b0e302086
        | exact resolve b0e302086 b0e302088
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e302086 b0e302088
      have b0e302230 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e302229
           have i₂ := b0e302184
           grind)
        | exact superpose b0e302184 b0e302229
        | exact resolve b0e302229 b0e302184
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e302184 b0e302229
      have b0e302231 : False := by grind
      exact b0e302231
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
        have b1e24 : y ≠ y ∨ x = (k x y) := by
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
        have b1e26 : x = (k x y) := by grind
        clear b1e24
        have b1e39 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e41 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e39
        have b1e42 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e41
             have r₂ := b1e23
             grind)
          | exact resolve b1e41 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e43 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e42
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e42
          | exact resolve b1e42 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e44 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e43
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e43
          | exact resolve b1e43 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e43
        have b1e45 : False := by grind
        exact b1e45
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : y ≠ y ∨ x = (k x y) := by
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
        have b2e24 : x = (k x y) := by grind
        clear b2e23
        have b2e43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e153 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e43 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43
        have b2e603 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e153 y x
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e153
          | (have j0 := b2e153 y x
             grind)
          | exact resolve b2e153 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e153
        have b2e606 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        clear b2e603
        have b2e609 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e606
             have r₂ := b2e22
             grind)
          | exact resolve b2e606 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e606
        have b2e613 : False := by grind
        exact b2e613
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        have b3e25 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b3e26 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b3e25
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
        have b3e28 : (k x y) = (τ (σ x)) := by
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
        have b3e29 : x = (k x y) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e28
          | exact resolve b3e28 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e51 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e52 : x = y ∨ y = (k x y) := by grind
        clear b3e51
        have b3e53 : y = (k x y) := by
          first
          | (have r₁ := b3e52
             have r₂ := b3e23
             grind)
          | exact resolve b3e52 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e55 : x = y := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e29
          | exact resolve b3e29 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e53
        have b3e57 : False := by grind
        exact b3e57
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y x) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : x ≠ y := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e21
            | exact resolve b4e21 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b4e59 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e29 X0 X1
               grind)
            | exact superpose b4e29 b4e14
            | exact resolve b4e14 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e69 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e59 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e59
            | exact resolve b4e59 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e185 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e51 x y
               grind)
            | exact superpose b4e51 b4e20
            | (have j1 := b4e51 x y
               grind)
            | exact resolve b4e20 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e198 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e199 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51
          have b4e662 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e198 (τ X1) (τ X0)
               have i₂ := b4e69 X1 X0
               grind)
            | exact superpose b4e69 b4e198
            | (have j0 := b4e198 (τ X1) (τ X0)
               grind)
            | exact resolve b4e198 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e675 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e662 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e662
            | (have j0 := b4e662 X0 X1
               grind)
            | exact resolve b4e662 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e662
          have b4e679 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e675 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e675
            | (have j0 := b4e675 X0 X1
               grind)
            | exact resolve b4e675 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e675
          have b4e682 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e679 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e679
            | (have j0 := b4e679 X0 X1
               grind)
            | exact resolve b4e679 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e679
          have b4e683 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e682 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e682
            | (have j0 := b4e682 X0 X1
               grind)
            | exact resolve b4e682 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e682
          have b4e684 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e683 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e683
            | (have j0 := b4e683 X0 X1
               grind)
            | exact resolve b4e683 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e683
          have b4e685 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e684 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e684
            | (have j0 := b4e684 X0 X1
               grind)
            | exact resolve b4e684 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e684
          have b4e707 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e199 (τ X1) (τ X0)
               have i₂ := b4e69 X1 X0
               grind)
            | exact superpose b4e69 b4e199
            | (have j0 := b4e199 (τ X1) (τ X0)
               grind)
            | exact resolve b4e199 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e718 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e707 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e707
            | (have j0 := b4e707 X0 X1
               grind)
            | exact resolve b4e707 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e707
          have b4e722 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e718 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e718
            | (have j0 := b4e718 X0 X1
               grind)
            | exact resolve b4e718 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e718
          have b4e725 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e722 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e722
            | (have j0 := b4e722 X0 X1
               grind)
            | exact resolve b4e722 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e722
          have b4e726 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e725 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e725
            | (have j0 := b4e725 X0 X1
               grind)
            | exact resolve b4e725 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e725
          have b4e727 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e726 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e726
            | (have j0 := b4e726 X0 X1
               grind)
            | exact resolve b4e726 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e726
          have b4e728 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e727 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e727
            | (have j0 := b4e727 X0 X1
               grind)
            | exact resolve b4e727 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e727
          have b4e742 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e185
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e185
            | (have j1 := b4e18 (σ y) (σ x)
               grind)
            | exact resolve b4e185 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e185
          have b4e743 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b4e742
          have b4e5477 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e743
               grind)
            | exact superpose b4e743 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e743
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e743
               grind)
            | exact resolve b4e17 b4e743
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e743
          have b4e5486 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b4e5477
          have b4e5487 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e5486
               have r₂ := b4e25
               grind)
            | exact resolve b4e5486 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5486
          have b4e5489 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e5487
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e5487
            | exact resolve b4e5487 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5487
          have b4e44045 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e5489
               grind)
            | exact superpose b4e5489 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e5489
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e5489
               grind)
            | exact resolve b4e16 b4e5489
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5489
          have b4e44055 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b4e44045
          have b4e44058 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e44055
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e44055
            | exact resolve b4e44055 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44055
          have b4e44820 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e44058
               grind)
            | exact superpose b4e44058 b4e14
            | exact resolve b4e14 b4e44058
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44058
          have b4e45028 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e44820
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e44820
            | exact resolve b4e44820 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44820
          have b4e45032 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b4e685 y x
               grind)
            | (have r₁ := b4e45028
               have r₂ := b4e685 y x
               grind)
            | exact resolve b4e45028 b4e685
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e685 b4e45028
          have b4e45475 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e45032
               grind)
            | exact superpose b4e45032 b4e14
            | exact resolve b4e14 b4e45032
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45032
          have b4e45686 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e45475
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e45475
            | exact resolve b4e45475 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45475
          have b4e45687 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b4e728 y x
               grind)
            | (have r₁ := b4e45686
               have r₂ := b4e728 y x
               grind)
            | exact resolve b4e45686 b4e728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e728 b4e45686
          have b4e46042 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e45687
               grind)
            | exact superpose b4e45687 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e45687
               grind)
            | exact resolve b4e17 b4e45687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46056 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
          clear b4e46042
          have b4e46057 : x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e46056
               have r₂ := b4e26
               grind)
            | exact resolve b4e46056 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46056
          have b4e46478 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e199 x y
               have i₂ := b4e46057
               grind)
            | exact superpose b4e46057 b4e199
            | (have j0 := b4e199 x y
               grind)
            | exact resolve b4e199 b4e46057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e199
          have b4e46526 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e46478
          have b4e315498 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e46526
               grind)
            | exact superpose b4e46526 b4e20
            | exact resolve b4e20 b4e46526
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46526
          have b4e317564 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e315498
               have i₂ := b4e45687
               grind)
            | exact superpose b4e45687 b4e315498
            | exact resolve b4e315498 b4e45687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45687 b4e315498
          have b4e317567 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b4e317564
          have b4e317568 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e317567
               have r₂ := b4e26
               grind)
            | exact resolve b4e317567 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e317567
          have b4e319612 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e317568
               grind)
            | exact superpose b4e317568 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e317568
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e317568
               grind)
            | exact resolve b4e16 b4e317568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e317568
          have b4e319624 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e319612
          have b4e319627 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e319624
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e319624
            | exact resolve b4e319624 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e319624
          have b4e323672 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e319627
               have i₂ := b4e46057
               grind)
            | exact superpose b4e46057 b4e319627
            | exact resolve b4e319627 b4e46057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46057
          have b4e323713 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e319627
               grind)
            | exact superpose b4e319627 b4e14
            | exact resolve b4e14 b4e319627
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e319627
          have b4e323925 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b4e323672
          have b4e323982 : y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e323713
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e323713
            | exact resolve b4e323713 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e323713
          have b4e324008 : x = (M.op x y) := by
            first
            | (have r₁ := b4e323925
               have r₂ := b4e25
               grind)
            | exact resolve b4e323925 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e323925
          have b4e324009 : y = (k y x) := by
            first
            | (have j1 := b4e16 y x
               grind)
            | (have r₁ := b4e323982
               have r₂ := b4e16 y x
               grind)
            | exact resolve b4e323982 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e323982
          have b4e327546 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e198 x y
               have i₂ := b4e324009
               grind)
            | exact superpose b4e324009 b4e198
            | (have j0 := b4e198 x y
               grind)
            | exact resolve b4e198 b4e324009
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e198
          have b4e327588 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e327546
          have b4e352188 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e327588
               grind)
            | exact superpose b4e327588 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e327588
               grind)
            | exact resolve b4e17 b4e327588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e327588
          have b4e352204 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e352188
          have b4e352205 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e352204
               have r₂ := b4e25
               grind)
            | exact resolve b4e352204 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e352204
          have b4e352208 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e352205
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e352205
            | exact resolve b4e352205 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e352205
          have b4e352210 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e352208
               have i₂ := b4e324009
               grind)
            | exact superpose b4e324009 b4e352208
            | exact resolve b4e352208 b4e324009
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e324009 b4e352208
          have b4e352211 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e352210
               have r₂ := b4e25
               grind)
            | exact resolve b4e352210 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e352210
          have b4e354052 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e352211
               grind)
            | exact superpose b4e352211 b4e20
            | exact resolve b4e20 b4e352211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e352211
          have b4e354069 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e354052
               have i₂ := b4e324008
               grind)
            | exact superpose b4e324008 b4e354052
            | exact resolve b4e354052 b4e324008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e324008 b4e354052
          have b4e354070 : False := by grind
          exact b4e354070
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y x) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e40 : x = y ∨ y = (k x y) := by grind
          clear b5e38
          have b5e41 : y = (k x y) := by
            first
            | (have r₁ := b5e40
               have r₂ := b5e25
               grind)
            | exact resolve b5e40 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e40
          have b5e44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e166 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e44 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e576 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e166 y x
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e166
            | (have j0 := b5e166 y x
               grind)
            | exact resolve b5e166 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e166
          have b5e579 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b5e576
          have b5e582 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e579
               have r₂ := b5e24
               grind)
            | exact resolve b5e579 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e579
          have b5e586 : False := by grind
          exact b5e586
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e24 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e23
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
        have b6e68 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
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
        have b6e70 : x = (M.op y x) ∨ y = (M.op y x) := by grind
        clear b6e68
        have b6e73 : y = (M.op y x) := by
          first
          | (have r₁ := b6e70
             have r₂ := b6e21
             grind)
          | exact resolve b6e70 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e76 : False := by grind
        exact b6e76
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y x) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b7e40 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e38
          have b7e41 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e40
               have r₂ := b7e25
               grind)
            | exact resolve b7e40 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e40
          have b7e42 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e41
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e41
            | exact resolve b7e41 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e45 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e42
               grind)
            | exact superpose b7e42 b7e14
            | exact resolve b7e14 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e46 : y = (k x y) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e45
            | exact resolve b7e45 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e56 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e57 : y = (M.op y x) ∨ x = (M.op y x) := by grind
          clear b7e56
          have b7e59 : x = (M.op y x) := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e21
               grind)
            | exact resolve b7e57 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e61 : False := by grind
          exact b7e61
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          clear b8e25
          have b8e45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e34 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e34
            | exact resolve b8e34 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34
          have b8e150 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e45 x y
               grind)
            | exact superpose b8e45 b8e20
            | (have j1 := b8e45 x y
               grind)
            | exact resolve b8e20 b8e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e160 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e45 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e161 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e45 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45
          have b8e517 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e160 (τ X1) (τ X0)
               have i₂ := b8e48 X1 X0
               grind)
            | exact superpose b8e48 b8e160
            | (have j0 := b8e160 (τ X1) (τ X0)
               grind)
            | exact resolve b8e160 b8e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e524 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e517 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e517
            | (have j0 := b8e517 X0 X1
               grind)
            | exact resolve b8e517 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e517
          have b8e527 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e524 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e524
            | (have j0 := b8e524 X0 X1
               grind)
            | exact resolve b8e524 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e524
          have b8e529 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e527 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e527
            | (have j0 := b8e527 X0 X1
               grind)
            | exact resolve b8e527 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e527
          have b8e530 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e529 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e529
            | (have j0 := b8e529 X0 X1
               grind)
            | exact resolve b8e529 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e529
          have b8e531 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e530 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e530
            | (have j0 := b8e530 X0 X1
               grind)
            | exact resolve b8e530 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e530
          have b8e532 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e531 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e531
            | (have j0 := b8e531 X0 X1
               grind)
            | exact resolve b8e531 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e531
          have b8e545 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e161 (τ X1) (τ X0)
               have i₂ := b8e48 X1 X0
               grind)
            | exact superpose b8e48 b8e161
            | (have j0 := b8e161 (τ X1) (τ X0)
               grind)
            | exact resolve b8e161 b8e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48
          have b8e552 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e545 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e545
            | (have j0 := b8e545 X0 X1
               grind)
            | exact resolve b8e545 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e545
          have b8e555 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e552 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e552
            | (have j0 := b8e552 X0 X1
               grind)
            | exact resolve b8e552 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e552
          have b8e557 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e555 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e555
            | (have j0 := b8e555 X0 X1
               grind)
            | exact resolve b8e555 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e555
          have b8e558 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e557 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e557
            | (have j0 := b8e557 X0 X1
               grind)
            | exact resolve b8e557 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e557
          have b8e559 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e558 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e558
            | (have j0 := b8e558 X0 X1
               grind)
            | exact resolve b8e558 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e558
          have b8e560 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e559 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e559
            | (have j0 := b8e559 X0 X1
               grind)
            | exact resolve b8e559 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e559
          have b8e569 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e150
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e150
            | (have j1 := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e150 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e150
          have b8e570 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e569
          have b8e3827 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e570
               grind)
            | exact superpose b8e570 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e570
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e570
               grind)
            | exact resolve b8e17 b8e570
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3833 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e570
          have b8e3835 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e3827
          have b8e3836 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e3835
               have r₂ := b8e3833
               grind)
            | exact resolve b8e3835 b8e3833
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3833 b8e3835
          have b8e3838 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e3836
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e3836
            | exact resolve b8e3836 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3836
          have b8e21528 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e3838
               grind)
            | exact superpose b8e3838 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e3838
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e3838
               grind)
            | exact resolve b8e16 b8e3838
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3838
          have b8e21538 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e21528
          have b8e21541 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e21538
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e21538
            | exact resolve b8e21538 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21538
          have b8e21626 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e21541
               grind)
            | exact superpose b8e21541 b8e14
            | exact resolve b8e14 b8e21541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21541
          have b8e21772 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e21626
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e21626
            | exact resolve b8e21626 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21626
          have b8e21775 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b8e532 y x
               grind)
            | (have r₁ := b8e21772
               have r₂ := b8e532 y x
               grind)
            | exact resolve b8e21772 b8e532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e532 b8e21772
          have b8e22296 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e21775
               grind)
            | exact superpose b8e21775 b8e14
            | exact resolve b8e14 b8e21775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21775
          have b8e22443 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e22296
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e22296
            | exact resolve b8e22296 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22296
          have b8e22444 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b8e560 y x
               grind)
            | (have r₁ := b8e22443
               have r₂ := b8e560 y x
               grind)
            | exact resolve b8e22443 b8e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e560 b8e22443
          have b8e22617 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e22444
               grind)
            | exact superpose b8e22444 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e22444
               grind)
            | exact resolve b8e17 b8e22444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e22627 : x ≠ y ∨ x = (M.op x y) := by grind
          have b8e22631 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
          clear b8e22617
          have b8e22632 : x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e22631
               have r₂ := b8e22627
               grind)
            | exact resolve b8e22631 b8e22627
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22631
          have b8e23256 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e161 x y
               have i₂ := b8e22632
               grind)
            | exact superpose b8e22632 b8e161
            | (have j0 := b8e161 x y
               grind)
            | exact resolve b8e161 b8e22632
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e161
          have b8e23304 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e23256
          have b8e214675 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e23304
               grind)
            | exact superpose b8e23304 b8e20
            | exact resolve b8e20 b8e23304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23304
          have b8e217916 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e214675
               have i₂ := b8e22444
               grind)
            | exact superpose b8e22444 b8e214675
            | exact resolve b8e214675 b8e22444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e214675
          have b8e217919 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b8e217916
          have b8e217920 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e217919
               have r₂ := b8e22627
               grind)
            | exact resolve b8e217919 b8e22627
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e217919
          have b8e219393 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e217920
               grind)
            | exact superpose b8e217920 b8e20
            | exact resolve b8e20 b8e217920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e219396 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e217920
               grind)
            | exact superpose b8e217920 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e217920
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e217920
               grind)
            | exact resolve b8e16 b8e217920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e217920
          have b8e219408 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e219396
          have b8e219411 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e219408
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e219408
            | exact resolve b8e219408 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219408
          have b8e220888 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e219393
               have i₂ := b8e22444
               grind)
            | exact superpose b8e22444 b8e219393
            | exact resolve b8e219393 b8e22444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22444 b8e219393
          have b8e220892 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e220888
               have r₂ := b8e22627
               grind)
            | exact resolve b8e220888 b8e22627
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22627 b8e220888
          have b8e224244 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e219411
               have i₂ := b8e22632
               grind)
            | exact superpose b8e22632 b8e219411
            | exact resolve b8e219411 b8e22632
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22632
          have b8e224285 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e219411
               grind)
            | exact superpose b8e219411 b8e14
            | exact resolve b8e14 b8e219411
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219411
          have b8e224497 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b8e224244
          have b8e224554 : y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e224285
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e224285
            | exact resolve b8e224285 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e224285
          have b8e224581 : x = (M.op x y) := by
            first
            | (have r₁ := b8e224497
               have r₂ := b8e220892
               grind)
            | exact resolve b8e224497 b8e220892
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e220892 b8e224497
          have b8e224582 : y = (k y x) := by
            first
            | (have j1 := b8e16 y x
               grind)
            | (have r₁ := b8e224554
               have r₂ := b8e16 y x
               grind)
            | exact resolve b8e224554 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e224554
          have b8e227392 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e160 x y
               have i₂ := b8e224582
               grind)
            | exact superpose b8e224582 b8e160
            | (have j0 := b8e160 x y
               grind)
            | exact resolve b8e160 b8e224582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160
          have b8e227434 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e227392
          have b8e250175 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e227434
               grind)
            | exact superpose b8e227434 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e227434
               grind)
            | exact resolve b8e17 b8e227434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e250187 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e227434
          have b8e250191 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e250175
          have b8e250192 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e250191
               have r₂ := b8e250187
               grind)
            | exact resolve b8e250191 b8e250187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e250191
          have b8e250195 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e250192
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e250192
            | exact resolve b8e250192 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e250192
          have b8e250197 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e250195
               have i₂ := b8e224582
               grind)
            | exact superpose b8e224582 b8e250195
            | exact resolve b8e250195 b8e224582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e224582 b8e250195
          have b8e250198 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e250197
               have r₂ := b8e250187
               grind)
            | exact resolve b8e250197 b8e250187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e250187 b8e250197
          have b8e251752 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e250198
               grind)
            | exact superpose b8e250198 b8e20
            | exact resolve b8e20 b8e250198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e250198
          have b8e251769 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e251752
               have i₂ := b8e224581
               grind)
            | exact superpose b8e224581 b8e251752
            | exact resolve b8e251752 b8e224581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e224581 b8e251752
          have b8e251770 : False := by grind
          exact b8e251770

/-- `Equation1516`: `x = (y ◇ y) ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation1516 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1516 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1516.models_iff G M).mp hM
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e61 : False := by grind
      exact b0e61
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
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b5e45 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e48 : x = y ∨ y = (k x y) := by grind
          clear b5e45
          have b5e49 : y = (k x y) := by
            first
            | (have r₁ := b5e48
               have r₂ := b5e21
               grind)
            | exact resolve b5e48 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e154 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e795 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e154 x y
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e154
            | (have j0 := b5e154 x y
               grind)
            | exact resolve b5e154 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e154
          have b5e798 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e795
          have b5e801 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e798
               have r₂ := b5e24
               grind)
            | exact resolve b5e798 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e798
          have b5e805 : False := by grind
          exact b5e805
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
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b7e45 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e47 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e48 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e47
               have r₂ := b7e23
               grind)
            | exact resolve b7e47 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e49 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e48
            | exact resolve b7e48 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e59 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e49
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e49 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e60 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e26
               grind)
            | exact resolve b7e59 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e59
          have b7e61 : x = y := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e22
               grind)
            | exact resolve b7e60 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e62 : False := by grind
          exact b7e62
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e113 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e122 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e113
               have r₂ := b8e24
               grind)
            | exact resolve b8e113 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e127 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e122
               have r₂ := b8e23
               grind)
            | exact resolve b8e122 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122
          have b8e130 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e127
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e127
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e127
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e127
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e127 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127
          have b8e131 : y = (M.op x y) ∨ x = y := by grind
          clear b8e130
          have b8e132 : x = y := by
            first
            | (have r₁ := b8e131
               have r₂ := b8e22
               grind)
            | exact resolve b8e131 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131
          have b8e133 : False := by grind
          exact b8e133

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        grind
      have b0e81 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e80 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80
      have b0e111 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e81 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e81
        | exact resolve b0e81 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e112 : (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e81 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e81
        | exact resolve b0e81 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81
      have b0e114 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e111
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e111
        | exact resolve b0e111 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111
      have b0e115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e114
           have i₂ := b0e112
           grind)
        | exact superpose b0e112 b0e114
        | exact resolve b0e114 b0e112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e112 b0e114
      have b0e116 : False := by grind
      exact b0e116
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e37 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e39 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e37
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e37
          | exact resolve b1e37 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e77 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e77 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e109 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e19
          | exact resolve b1e19 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e130 : (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e78 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e78
          | exact resolve b1e78 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78
        have b1e136 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e109
             have i₂ := b1e130
             grind)
          | exact superpose b1e130 b1e109
          | exact resolve b1e109 b1e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e109 b1e130
        have b1e138 : False := by grind
        exact b1e138
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e70 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e71 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e70 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e251 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0
             have i₂ := b2e52 X0 X1
             grind)
          | (have i₁ := b2e71 X0
             have i₂ := b2e52 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e52 b2e71
          | (have j1 := b2e52 X1 X0
             grind)
          | exact resolve b2e71 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e71
        have b2e270 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e251 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e251
        have b2e557 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e270 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e270
        have b2e558 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e557 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e557
        have b2e634 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e558 (σ X0)
             grind)
          | exact superpose b2e558 b2e18
          | exact resolve b2e18 b2e558
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e641 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e634 X0
             have i₂ := b2e558 X0
             grind)
          | exact superpose b2e558 b2e634
          | exact resolve b2e634 b2e558
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e558 b2e634
        have b2e890 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e641 x
             grind)
          | exact superpose b2e641 b2e21
          | exact resolve b2e21 b2e641
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e641
        have b2e915 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e890
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e890
          | exact resolve b2e890 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e890
        have b2e916 : False := by grind
        exact b2e916
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e38 : (M.op x y) = (k y x) := by grind
        have b3e67 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b3e80 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e67
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e67
          | exact resolve b3e67 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e81 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e80
          | exact resolve b3e80 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e82 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b3e81
             have r₂ := b3e19
             grind)
          | exact resolve b3e81 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e92 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e82
        have b3e93 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e92
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e92
          | exact resolve b3e92 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92
        have b3e94 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e93
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e93
          | exact resolve b3e93 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e93
        have b3e95 : False := by grind
        exact b3e95
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e43 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e44 : (M.op x y) = (k y x) := by grind
          have b4e46 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e43
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e43
            | exact resolve b4e43 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e47 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e46
               have i₂ := b4e44
               grind)
            | exact superpose b4e44 b4e46
            | exact resolve b4e46 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e46
          have b4e48 : False := by grind
          exact b4e48
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e78 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e248 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e79 X0
               have i₂ := b5e59 X0 X1
               grind)
            | (have i₁ := b5e79 X0
               have i₂ := b5e59 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e59 b5e79
            | (have j1 := b5e59 X1 X0
               grind)
            | exact resolve b5e79 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e79
          have b5e265 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e248 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248
          have b5e542 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e265 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e265
          have b5e543 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e542 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e542
          have b5e617 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e543 (σ X0)
               grind)
            | exact superpose b5e543 b5e19
            | exact resolve b5e19 b5e543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e624 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e617 X0
               have i₂ := b5e543 X0
               grind)
            | exact superpose b5e543 b5e617
            | exact resolve b5e617 b5e543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e543 b5e617
          have b5e874 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e624 y
               grind)
            | exact superpose b5e624 b5e24
            | exact resolve b5e24 b5e624
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e624
          have b5e898 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e874
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e874
            | exact resolve b5e874 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e874
          have b5e899 : False := by grind
          exact b5e899
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e35 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b6e38 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e35
          | exact resolve b6e35 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          grind
        have b6e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e81 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e82 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e81 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e95 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e82 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e82
          | exact resolve b6e82 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e102 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e95
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e95
          | exact resolve b6e95 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e124 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e102
             grind)
          | exact superpose b6e102 b6e19
          | exact resolve b6e19 b6e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102
        have b6e221 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e82 X0
             have i₂ := b6e58 X0 X1
             grind)
          | (have i₁ := b6e82 X0
             have i₂ := b6e58 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e58 b6e82
          | (have j1 := b6e58 X1 X0
             grind)
          | exact resolve b6e82 b6e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58 b6e82
        have b6e243 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e221 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e221
        have b6e324 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e124
             have i₂ := b6e63 x y
             grind)
          | exact superpose b6e63 b6e124
          | (have j1 := b6e63 x y
             grind)
          | exact resolve b6e124 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63 b6e124
        have b6e355 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        clear b6e324
        have b6e365 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e355
             have r₂ := b6e20
             grind)
          | exact resolve b6e355 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e355
        have b6e1717 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e66 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e66
          | exact resolve b6e66 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e1954 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1717
        have b6e2034 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1954
             grind)
          | exact superpose b6e1954 b6e13
          | exact resolve b6e13 b6e1954
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1954
        have b6e2048 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2034
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2034
          | exact resolve b6e2034 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2034
        have b6e2326 : y = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e243 x x
             have i₂ := b6e2048
             grind)
          | exact superpose b6e2048 b6e243
          | exact resolve b6e243 b6e2048
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e243 b6e2048
        have b6e2327 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e2326
        have b6e2339 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e2327
             have r₂ := b6e20
             grind)
          | exact resolve b6e2327 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2327
        have b6e2647 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e2339
             grind)
          | exact superpose b6e2339 b6e19
          | exact resolve b6e19 b6e2339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2650 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e38
             have i₂ := b6e2339
             grind)
          | exact superpose b6e2339 b6e38
          | exact resolve b6e38 b6e2339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e2657 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e2339
             grind)
          | exact superpose b6e2339 b6e13
          | exact resolve b6e13 b6e2339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2674 : x = y := by
          first
          | (have i₁ := b6e2657
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e2657
          | exact resolve b6e2657 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2657
        have b6e2679 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e2650
             have i₂ := b6e365
             grind)
          | exact superpose b6e365 b6e2650
          | exact resolve b6e2650 b6e365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e365 b6e2650
        have b6e2681 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e2647
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e2647
          | exact resolve b6e2647 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2647
        have b6e2688 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b6e2679
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e2679
          | exact resolve b6e2679 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2679
        have b6e2690 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e2681
             have i₂ := b6e2339
             grind)
          | exact superpose b6e2339 b6e2681
          | exact resolve b6e2681 b6e2339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2681
        have b6e2696 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b6e2688
             have i₂ := b6e2339
             grind)
          | exact superpose b6e2339 b6e2688
          | exact resolve b6e2688 b6e2339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2339 b6e2688
        have b6e2697 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e2690
             have i₂ := b6e2674
             grind)
          | exact superpose b6e2674 b6e2690
          | exact resolve b6e2690 b6e2674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2690
        have b6e2698 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e2696
             have i₂ := b6e2674
             grind)
          | exact superpose b6e2674 b6e2696
          | exact resolve b6e2696 b6e2674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2674 b6e2696
        have b6e2699 : False := by grind
        exact b6e2699
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e89 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e90 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e89 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e386 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e90 X0
               have i₂ := b7e69 X0 X1
               grind)
            | (have i₁ := b7e90 X0
               have i₂ := b7e69 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e69 b7e90
            | (have j1 := b7e69 X1 X0
               grind)
            | exact resolve b7e90 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69 b7e90
          have b7e411 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e386 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e386
          have b7e1602 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e411 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e411
          have b7e1603 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e1602 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1602
          have b7e1724 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e1603 (σ X0)
               grind)
            | exact superpose b7e1603 b7e19
            | exact resolve b7e19 b7e1603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1731 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e1724 X0
               have i₂ := b7e1603 X0
               grind)
            | exact superpose b7e1603 b7e1724
            | exact resolve b7e1724 b7e1603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1603 b7e1724
          have b7e2720 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e1731 y
               grind)
            | exact superpose b7e1731 b7e24
            | exact resolve b7e24 b7e1731
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1731
          have b7e3376 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e2720
               grind)
            | exact superpose b7e2720 b7e14
            | exact resolve b7e14 b7e2720
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2720
          have b7e3395 : x = (M.op y y) := by
            first
            | (have i₁ := b7e3376
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e3376
            | exact resolve b7e3376 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3376
          have b7e3400 : False := by grind
          exact b7e3400
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e196 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e64 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e197 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e196
               have r₂ := b8e24
               grind)
            | exact resolve b8e196 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e196
          have b8e198 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e197
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e197
            | exact resolve b8e197 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e197
          have b8e199 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e198
               grind)
            | exact superpose b8e198 b8e20
            | exact resolve b8e20 b8e198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e198
          have b8e208 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e199
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e199
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e199 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e199
          have b8e209 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e208
          have b8e210 : x = (M.op y y) := by
            first
            | (have r₁ := b8e209
               have r₂ := b8e21
               grind)
            | exact resolve b8e209 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209
          have b8e212 : False := by grind
          exact b8e212

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1728 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
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
      have b0e57 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e60 : False := by grind
      exact b0e60
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
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
          have b5e45 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e48 : x = y ∨ x = (k x y) := by grind
          clear b5e45
          have b5e49 : x = (k x y) := by
            first
            | (have r₁ := b5e48
               have r₂ := b5e21
               grind)
            | exact resolve b5e48 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e116 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e747 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e116 x y
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e116
            | (have j0 := b5e116 x y
               grind)
            | exact resolve b5e116 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e116
          have b5e752 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e747
          have b5e757 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e752
               have r₂ := b5e24
               grind)
            | exact resolve b5e752 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e752
          have b5e764 : False := by grind
          exact b5e764
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
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
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
          have b7e44 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e44
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
          have b7e58 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e48
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e48 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e59 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e26
               grind)
            | exact resolve b7e58 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e58
          have b7e60 : x = y := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e22
               grind)
            | exact resolve b7e59 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e61 : False := by grind
          exact b7e61
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
          have b8e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e89 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e54 x y
               grind)
            | exact superpose b8e54 b8e20
            | (have j1 := b8e54 x y
               grind)
            | exact resolve b8e20 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e99 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e89
               have r₂ := b8e24
               grind)
            | exact resolve b8e89 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e104 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e99
               have r₂ := b8e23
               grind)
            | exact resolve b8e99 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99
          have b8e105 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e104
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e104
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e104
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e104
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e104 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e106 : x = (M.op x y) ∨ x = y := by grind
          clear b8e105
          have b8e107 : x = y := by
            first
            | (have r₁ := b8e106
               have r₂ := b8e22
               grind)
            | exact resolve b8e106 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106
          have b8e108 : False := by grind
          exact b8e108
